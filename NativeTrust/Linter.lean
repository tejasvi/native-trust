import Lean
import NativeTrust.Kernelize
import NativeTrust.KernelBudget

/-!
# A write-time linter: does this native fact need compiled code at all?

With `set_option linter.nativeTrust true`, every `native_decide`/`bv_decide`/`decide +native` fact
of the file is checked as it is added.

1. **Blocked.** A static triage (no evaluation, milliseconds): if a constant that Lean's kernel
   cannot evaluate is reachable from the decided term, the linter warns and names it, with the
   chain of definitions leading to it. Such a fact rests on compiled code for good: it can never be
   re-proved by the kernel, independent checkers cannot check it, and `lake check` and Comparator
   reject anything that uses it. The platform word size (`System.Platform.getNumBits`, reached through
   `USize`, `HashMap`, `HashSet`) alone does not count: NativeTrust's platform case split converts such
   a fact when its result is the same on 32- and 64-bit platforms.
2. **Unnecessary.** For a `native_decide`/`decide +native` fact without such a constant, the linter
   asks the kernel to evaluate `decide p = true` itself, within a small budget
   (`nativeTrust.kernelHeartbeats`, thousands of heartbeats, deterministic). If the kernel succeeds,
   compiled code was not needed: the linter warns "native_decide is unnecessary here: decide +kernel
   proves it (N ms)" and offers `decide +kernel` as a "Try this" replacement at the tactic. With
   `linter.nativeTrust.strict` this is an error (a CI policy). In a study of 52,821 native facts in
   16 public packages, 51,307 of the 51,329 conversions succeeded with plain kernel evaluation.

The check uses the ambient `maxRecDepth`, as `decide +kernel` does. Facts that it cannot settle
within the budget get no warning; `#native_decide_audit` lists every native fact of a module with
its verdict (replaceable by `decide +kernel`, needs NativeTrust's transformations, blocked, too
expensive within the budget).

The triage over-approximates: a constant on a branch that the evaluation never takes still counts
(panic and trace messages, and proofs, are already excluded).
-/

open Lean Elab Command Meta

namespace NativeTrust

register_option linter.nativeTrust : Bool := {
  defValue := false
  descr := "NativeTrust: warn when a native_decide/bv_decide fact can never be checked by Lean's \
    kernel (static triage of the constants it reaches)"
}

register_option linter.nativeTrust.unnecessary : Bool := {
  defValue := true
  descr := "NativeTrust: with `linter.nativeTrust`, also evaluate each new native_decide/decide \
    +native fact without blockers in the kernel (budget `nativeTrust.kernelHeartbeats`) and warn, \
    with a `decide +kernel` suggestion, when the kernel proves it"
}

register_option linter.nativeTrust.strict : Bool := {
  defValue := false
  descr := "NativeTrust: report 'native_decide is unnecessary here' as an error instead of a \
    warning (a CI policy)"
}

/-- Native axioms of the current file already triaged. -/
initialize lintState : IO.Ref NameSet ← IO.mkRef {}

/-- Native axioms without a recorded source range already claimed by the plain kernel check (claimed
atomically: linters of different commands run concurrently). Facts with a range need no claim: only
the command whose source contains the range checks them, also when the file is elaborated again. -/
initialize kernelLintState : IO.Ref NameSet ← IO.mkRef {}

/-- `findBlockers` results already computed in this process, keyed by the term, `static` and the number
of registered replacements (`@[kernel_replace]`, `@[kernel_replace_retry]`, `@[kernel_fold]`; facts
repeated by `all_goals` are triaged once). -/
initialize blockersCache : IO.Ref (Std.HashMap (Expr × Bool × Nat) (Array Blocker)) ← IO.mkRef {}

/-- `findBlockers e (static := static)`, cached. The static triage (blocked constructs) counts the
retry with retry-only replacements as NativeTrust's (`retryRepl`): a fact that only the retry converts
is not blocked. -/
def cachedBlockers (e : Expr) (static : Bool) : CoreM (Array Blocker) := do
  let env ← getEnv
  let key := (e, static, (kernelReplaceExt.getState env).size + (kernelRetryReplaceExt.getState env).size +
    (foldExt.getState env).size)
  if let some bs := (← blockersCache.get)[key]? then return bs
  let bs ← findBlockers e (static := static) (retryRepl := static)
  blockersCache.modify (·.insert key bs)
  return bs

/-- Is `System.Platform.getNumBits` the only blocker? Then NativeTrust's platform case split
(`proveTrueByKernelPlatform`) can still convert the fact, when its result is the same for both word sizes. -/
def onlyPlatformBlocker (blockers : Array Blocker) : Bool :=
  !blockers.isEmpty && blockers.all (·.name == ``System.Platform.getNumBits)

/-- The static triage: the blockers of `e`, none when the only one is the word size (`onlyPlatformBlocker`). -/
def triageBlockers (e : Expr) : CoreM (Array Blocker) := do
  let bs ← cachedBlockers e true
  return if onlyPlatformBlocker bs then #[] else bs

/-! ## Plain kernel evaluation within a budget -/

/-- Evaluate `e = true` (a closed `Bool` term with universe parameters `lvls`) in the kernel, as
`decide +kernel` does (ambient `maxRecDepth`), within `heartbeats` thousand heartbeats. Nothing is
added to the environment. -/
def plainKernelCheck (e : Expr) (lvls : List Name) (heartbeats : Nat) : CoreM PlainVerdict := do
  let recDepth := maxRecDepth.get (← getOptions)
  withoutModifyingEnv do
    let name := Name.mkNum `_nativeTrust_plain_check (hash e).toNat
    let t0 ← IO.monoMsNow
    match ← tryAddTheorem name lvls (mkBoolEq e boolTrue) (reflBool boolTrue)
        { maxHeartbeats := heartbeats, maxRecDepth := recDepth } with
    | .ok ms => return .proved ms
    | .error ex => classifyKernelFailure ex ((← IO.monoMsNow) - t0)

/-! ## Where a native fact comes from -/

/-- Is `stx` a `native_decide` or `decide +native` tactic? -/
def isNativeTacticSyntax (stx : Syntax) : Bool :=
  stx.isOfKind ``Lean.Parser.Tactic.nativeDecide ||
    (stx.isOfKind ``Lean.Parser.Tactic.decide &&
      (stx[1].find? fun s => s.isIdent && s.getId == `native).isSome)

/-- The `native_decide`/`decide +native` tactics in `stx`. -/
partial def nativeTacticsIn (stx : Syntax) : Array Syntax :=
  go stx #[]
where
  go (stx : Syntax) (acc : Array Syntax) : Array Syntax :=
    let acc := if isNativeTacticSyntax stx then acc.push stx else acc
    stx.getArgs.foldl (fun acc a => go a acc) acc

/-- Start position (line, column) of the declaration range of `ax`: for native axioms, Lean records
the range of the tactic that made them. -/
def nativeAxiomPos? (ax : Name) : CoreM (Option Position) := do
  return (← findDeclarationRanges? ax).map (·.range.pos)

def posLe (a b : Position) : Bool := a.line < b.line || (a.line == b.line && a.column ≤ b.column)

/-! ## The linter -/

/-- The plain kernel check on the native facts `fresh` (axiom, decided term, universe parameters)
that belong to command `stx` and have no blocker. A fact belongs to the command whose source range
contains the range Lean recorded for it (the tactic); facts without a recorded range are claimed by
the first linter run that sees them. Facts made by one tactic call (`all_goals native_decide`) are
reported together, and `decide +kernel` is suggested only when the kernel proves all of them. -/
def unnecessaryCheck (stx : Syntax) (fresh : Array (Name × Expr × List Name)) : CommandElabM Unit := do
  let opts ← getOptions
  let budget := nativeTrust.kernelHeartbeats.get opts
  let fileMap ← getFileMap
  let range? : Option (Position × Position) := do
    let p ← stx.getPos?
    let q ← stx.getTailPos?
    return (fileMap.toPosition p, fileMap.toPosition q)
  let tactics := nativeTacticsIn stx
  -- facts of this command (with the position of their tactic, if recorded)
  let mut mine : Array (Name × Expr × List Name × Option Position) := #[]
  for (ax, e, lvls) in fresh do
    let tac := nativeTacticOf ax
    unless tac == `native_decide || tac == `decide do continue
    let pos? ← liftCoreM (nativeAxiomPos? ax)
    match pos?, range? with
    | some p, some (a, b) => if posLe a p && posLe p b then mine := mine.push (ax, e, lvls, some p)
    | _, _ => mine := mine.push (ax, e, lvls, none)
  if mine.isEmpty then return
  -- facts without a range: claim atomically
  let noRange := mine.filter (·.2.2.2.isNone)
  let claimedNoRange ← if noRange.isEmpty then pure #[] else
    kernelLintState.modifyGet fun s =>
      (noRange.filter (!s.contains ·.1), noRange.foldl (fun s f => s.insert f.1) s)
  let claimed := mine.filter (·.2.2.2.isSome) ++ claimedNoRange
  if claimed.isEmpty then return
  -- group by tactic position
  let mut groups : Array (Option Position × Array (Name × PlainVerdict × Bool)) := #[]
  let key (e : Expr) : Expr × Nat × Nat := (e, budget, maxRecDepth.get opts)
  for (ax, e, lvls, pos?) in claimed do
    -- facts with blockers get the blocked-construct warning instead
    unless (← liftCoreM (triageBlockers e)).isEmpty do continue
    let (v, cached) ← match (← plainAttempts.get)[key e]? with
      | some v => pure (v, true)
      | none => do
        let v ← liftCoreM (plainKernelCheck e lvls budget)
        plainAttempts.modify (·.insert (key e) v)
        pure (v, false)
    match groups.findIdx? (·.1 == pos?) with
    | some i => groups := groups.modify i fun (p, vs) => (p, vs.push (ax, v, cached))
    | none => groups := groups.push (pos?, #[(ax, v, cached)])
  let strict := linter.nativeTrust.strict.get opts
  for (pos?, vs) in groups do
    let mut total := 0
    let mut allProved := true
    for (_, v, cached) in vs do
      match v with
      | .proved ms => unless cached do total := total + ms
      | _ => allProved := false
    unless allProved do continue
    let tacName := nativeTacticOf vs[0]!.1
    -- the tactic's syntax in this command, found by its position
    let tacStx? := tactics.find? fun t => match t.getPos?, pos? with
      | some p, some q => fileMap.toPosition p == q
      | _, _ => false
    let tacStx? := tacStx? <|> (if tactics.size == 1 && pos?.isNone then tactics[0]? else none)
    let ref := tacStx?.getD stx
    let what := if vs.size == 1 then m!"decide +kernel proves it ({total} ms)"
      else m!"decide +kernel proves all {vs.size} goals ({total} ms)"
    let msg := m!"{nativeTacticDisplay tacName} is unnecessary here: {what}\n\
      note: this check can be disabled with `set_option linter.nativeTrust.unnecessary false`"
    if strict then logErrorAt ref msg else logWarningAt ref msg
    if let some t := tacStx? then
      liftCoreM <| Lean.Meta.Tactic.TryThis.addSuggestion t
        ({ suggestion := .string "decide +kernel" } : Lean.Meta.Tactic.TryThis.Suggestion)

def nativeTrustLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless linter.nativeTrust.get (← getOptions) do return
    let env ← getEnv
    let checkK := linter.nativeTrust.unnecessary.get (← getOptions)
    let claimedK ← kernelLintState.get
    let mut done ← lintState.get
    let mut msgs : Array MessageData := #[]
    let mut cands : Array (Name × Expr × List Name) := #[]
    for (ax, ci) in env.constants.map₂.toList do
      unless isNativeAxiom env ax do continue
      let newT := !done.contains ax
      -- the plain kernel check keeps its own record: the run that triages a fact first need not be
      -- the run of the command that made it
      let newK := checkK && !claimedK.contains ax
      unless newT || newK do continue
      let some (_, e, _) := ci.type.eq? | continue
      if newT then
        done := done.insert ax
        let blockers ← liftCoreM (triageBlockers e)
        unless blockers.isEmpty do
          msgs := msgs.push <| m!"native fact `{privateToUserName ax}` can never be checked by \
            Lean's kernel: it reaches constants without a kernel definition\n" ++
            MessageData.joinSep (blockers.toList.map Blocker.toMessageData) "\n"
      if newK then cands := cands.push (ax, e, ci.levelParams)
    lintState.set done
    unless msgs.isEmpty do
      logWarningAt stx (MessageData.joinSep msgs.toList "\n\n" ++
        m!"\n\nnote: this linter can be disabled with `set_option linter.nativeTrust false`")
    unless cands.isEmpty do
      unnecessaryCheck stx cands

initialize addLinter nativeTrustLinter

/-! ## `#native_decide_audit` -/

/-- Verdict of `#native_decide_audit` on one native fact. -/
inductive AuditVerdict where
  | replaceable (ms : Nat)
  | nativeTrust (why : String) (ms : Nat)
  | blocked (blockers : Array Blocker)
  | expensive (why : String)
  | stuck (why : String)

def AuditVerdict.tag : AuditVerdict → String
  | .replaceable .. => "REPLACEABLE"
  | .nativeTrust .. => "NATIVETRUST"
  | .blocked .. => "BLOCKED"
  | .expensive .. => "EXPENSIVE"
  | .stuck .. => "STUCK"

/-- Why plain kernel evaluation cannot run `e` although NativeTrust's copies can: well-founded
recursion or registered `@[kernel_replace]` replacements reachable from `e`. -/
def transformReason (e : Expr) : CoreM (Option String) := do
  if onlyPlatformBlocker (← cachedBlockers e true) then
    return some "the platform word size (`System.Platform.getNumBits`): the case split over `numBits = 32 ∨ \
      numBits = 64` evaluates both"
  let raw ← cachedBlockers e false
  if let some b := raw.find? (·.name == ``WellFounded.fix) then
    return some s!"well-founded recursion via {" → ".intercalate (b.path.map toString)}"
  let user := kernelReplaceExt.getState (← getEnv)
  let retry := kernelRetryReplaceExt.getState (← getEnv)
  let mut seen : NameSet := {}
  let mut todo := e.getUsedConstants
  while h : 0 < todo.size do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if user.contains c then return some s!"`{c}` has a registered @[kernel_replace] replacement"
    -- the retry's replacements (`@[kernel_replace_retry]`, e.g. `NativeTrust.StrLib`), worded the same
    if retry.contains c then return some s!"`{c}` has a registered @[kernel_replace] replacement"
    if let some (.defnInfo d) := (← getEnv).find? c then
      todo := todo ++ d.value.getUsedConstants
  return none

/-- The verdict on native fact `ax : e = true`, with `budget` thousand heartbeats for each kernel
evaluation. -/
def auditFact (ax : Name) (e : Expr) (lvls : List Name) (budget : Nat) : MetaM AuditVerdict := do
  let blockers ← cachedBlockers e true
  let platform := onlyPlatformBlocker blockers
  unless blockers.isEmpty || platform do return .blocked blockers
  let bv := nativeTacticOf ax == `bv_decide
  match ← plainKernelCheck e lvls budget with
  | .proved ms => return if bv then .nativeTrust "kernel evaluation of the certificate check" ms
      else .replaceable ms
  | v =>
    let why? ← transformReason e
    let plainWhy := match v with
      | .budget _ => s!"not within {budget} thousand heartbeats"
      | .resources m => m
      | .notTrue m => m
      | .proved _ => ""
    -- no copy or replacement would change the evaluation: the plain result stands
    if why?.isNone then
      if let .budget _ := v then
        return .expensive s!"no blocker, but the kernel did not finish within {budget} thousand \
          heartbeats (`set_option nativeTrust.kernelHeartbeats`; `kdecide (config := \{ split := n })`)"
    -- NativeTrust's route: copies for well-founded recursion, registered replacements, a high
    -- `maxRecDepth`; within the same budget
    let r ← withoutModifyingEnv do
      let name := Name.mkNum `_nativeTrust_audit_check (hash e).toNat
      try
        let r ← proveTrueByKernel e name lvls
          { maxHeartbeats := budget, native := false, diagnoseFalse := false, accFallback := false,
            blockedHeartbeats := budget }
        pure (Except.ok r.ms)
      catch ex => pure (Except.error (← ex.toMessageData.toString))
    match r with
    | .ok ms =>
      let why := why?.getD s!"`decide +kernel` fails: {plainWhy}"
      return .nativeTrust s!"{why}; `kdecide`/`kernelize` prove it" ms
    | .error msg =>
      if (msg.splitOn "deterministic timeout").length > 1 || (msg.splitOn "heartbeats").length > 1 then
        return .expensive s!"needs NativeTrust's transformations ({why?.getD plainWhy}) and did \
          not finish within {budget} thousand heartbeats"
      -- the word size: the case split does not prove it (its result differs between 32 and 64 bits, or
      -- the evaluation gets stuck), so the fact stays native
      if platform then return .blocked blockers
      return .stuck s!"the kernel does not reduce it to `true`: {firstLine plainWhy}"

/-- `#native_decide_audit` lists every native fact (`native_decide`, `decide +native`, `bv_decide`)
of the current module, and `#native_decide_audit M` those of the imported module `M`, each with a
verdict:
* `REPLACEABLE`: `decide +kernel` proves it within the budget (`nativeTrust.kernelHeartbeats`);
* `NATIVETRUST`: plain kernel evaluation does not, but NativeTrust's transformations do
  (well-founded recursion, registered replacements, the case split over the word size; `kdecide`,
  `kernelize`);
* `BLOCKED`: it reaches a constant that the kernel cannot evaluate (named, with the path); when the only
  one is the word size (`System.Platform.getNumBits`), after the case split has failed on it (its
  result differs between 32 and 64 bits, or the evaluation gets stuck);
* `EXPENSIVE`: no blocker, but the kernel does not finish within the budget;
* `STUCK`: the kernel finishes without reducing it to `true` (a cast in an instance, say). -/
syntax (name := nativeDecideAuditCmd) "#native_decide_audit" (ppSpace ident)? : command

@[command_elab nativeDecideAuditCmd] def elabNativeDecideAudit : CommandElab := fun stx =>
  liftTermElabM do
    let env ← getEnv
    let budget := nativeTrust.kernelHeartbeats.get (← getOptions)
    let (modName, axs) ← if stx[1].isNone then do
        -- current module: wait for every declaration (`constants` blocks on asynchronous proofs)
        let mut l : Array (Name × Option Position) := #[]
        for (n, _) in env.constants.map₂.toList do
          if isNativeAxiom env n then l := l.push (n, ← nativeAxiomPos? n)
        let sorted := l.qsort fun (a, p) (b, q) => match p, q with
          | some p, some q => p.line < q.line || (p.line == q.line && p.column < q.column) ||
              (p == q && a.toString < b.toString)
          | some _, none => true
          | none, some _ => false
          | none, none => a.toString < b.toString
        pure (env.mainModule, sorted.map (·.1))
      else do
        let mod := stx[1][0].getId
        pure (mod, (← nativeAxiomsIn mod).map (·.1))
    let mut lines : Array MessageData := #[]
    let mut counts : Std.HashMap String Nat := {}
    for ax in axs do
      let some (.axiomInfo info) := env.find? ax | continue
      let some (_, e, _) := info.type.eq? | continue
      let v ← auditFact ax e info.levelParams budget
      counts := counts.insert v.tag (counts.getD v.tag 0 + 1)
      let fact := m!"`{privateToUserName ax}` ({nativeTacticDisplay (nativeTacticOf ax)})"
      lines := lines.push <| match v with
        | .replaceable ms => m!"REPLACEABLE {fact}: `decide +kernel` proves it ({ms} ms)"
        | .nativeTrust why ms => m!"NATIVETRUST {fact}: {why} ({ms} ms)"
        | .blocked bs => m!"BLOCKED {fact}: " ++
            MessageData.joinSep (bs.toList.map fun b => m!"`{b.name}`") ", " ++ m!"\n" ++
            MessageData.joinSep (bs.toList.map Blocker.toMessageData) "\n"
        | .expensive why => m!"EXPENSIVE {fact}: {why}"
        | .stuck why => m!"STUCK {fact}: {why}"
    let c (t : String) := counts.getD t 0
    let summary := m!"#native_decide_audit `{modName}`: {axs.size} native facts: \
      {c "REPLACEABLE"} replaceable by `decide +kernel`, {c "NATIVETRUST"} need NativeTrust \
      transformations, {c "BLOCKED"} blocked, {c "EXPENSIVE"} too expensive within the budget \
      ({budget} thousand heartbeats), {c "STUCK"} stuck"
    report (MessageData.joinSep (summary :: lines.toList) "\n")

end NativeTrust
