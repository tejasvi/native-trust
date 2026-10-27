import Lean
import NativeTrust.Kernel

/-!
# Re-proving existing `native_decide` theorems: `kernelize`

`native_decide` (and `bv_decide`) add one axiom per use, `<decl>._native.<tactic>.ax… : e = true`,
asserting the result of compiled evaluation. `kernelize T` re-proves `T` without them:

1. it finds every such axiom that `T` depends on (through any chain of lemmas and definitions);
2. it proves each statement `e = true` by kernel evaluation (`proveTrueByKernel`);
3. it rebuilds every lemma and definition between `T` and those axioms, with the axioms replaced
   by the kernel proofs;
4. it adds `T.kernel` (or the name given with `as`) whose statement is `T`'s statement,
   expression for expression, and checks that it depends on no axiom beyond `propext`,
   `Classical.choice` and `Quot.sound`.

`T` and the modules it comes from stay untouched, so a kernel track can live in a separate
module that imports a native_decide build. Older toolchains used the axiom `Lean.ofReduceBool`
instead of per-use axioms; its uses `Lean.ofReduceBool a b h` are replaced the same way.
-/

open Lean Meta Elab Command

namespace NativeTrust

/-- Axioms added by `Lean.Meta.nativeEqTrue` for `native_decide`/`bv_decide`. -/
def isNativeAxiom (env : Environment) (n : Name) : Bool :=
  n.components.contains `_native && (env.find? n matches some (.axiomInfo _))

/-- Toolchains before v4.29 asserted native evaluation through these global axioms instead of
per-use axioms; `kernelize` replaces the uses `Lean.ofReduceBool a true h` directly. -/
def isLegacyNativeAxiom (n : Name) : Bool :=
  n == `Lean.ofReduceBool || n == `Lean.ofReduceNat || n == `Lean.trustCompiler

/-- Native axioms that constant `c` depends on. -/
def nativeAxiomsOfCore (c : Name) : CoreM (Array Name) := do
  let env ← getEnv
  return (← collectAxioms c).filter fun a => isNativeAxiom env a || isLegacyNativeAxiom a

/-- Registry of kernel proofs of native facts: native axiom `ax : e = true` ↦ a theorem with the
same statement proved by kernel evaluation. Persistent, so a module can reuse the proofs made in
the modules it imports (e.g. one module per fact, built in parallel, then one assembly module). -/
initialize nativeProofExt : SimplePersistentEnvExtension (Name × Name) (NameMap Name) ←
  registerSimplePersistentEnvExtension {
    addEntryFn := fun m (a, b) => m.insert a b
    addImportedFn := fun arrs =>
      arrs.foldl (fun m arr => arr.foldl (fun m (a, b) => m.insert a b) m) {}
  }

/-- Proofs registered with `@[kernel_fact]`. -/
initialize kernelFactExt : SimpleScopedEnvExtension Name (Array Name) ←
  registerSimpleScopedEnvExtension { initial := #[], addEntry := (·.push ·) }

/-- `@[kernel_fact] theorem h : P` registers `h` as the proof of `P` to use for every native fact
`decide P = true` (for instance a primality fact proved by a certificate or by `norm_num`) instead
of evaluating the decision procedure in the kernel. `h` itself must depend only on the standard
axioms. -/
initialize registerBuiltinAttribute {
    name := `kernel_fact
    descr := "NativeTrust: proof of `P` used for native facts `decide P = true`"
    add := fun decl _ kind => do
      let info ← getConstInfo decl
      unless info matches .thmInfo _ do
        throwError "@[kernel_fact]: `{decl}` must be a theorem"
      unless info.levelParams.isEmpty do
        throwError "@[kernel_fact]: `{decl}` must not be universe polymorphic"
      kernelFactExt.add decl kind
  }

/-- A registered `@[kernel_fact]` proof of `p` (syntactically equal, or equal up to reducible
unfolding). -/
def findKernelFact? (p : Expr) : MetaM (Option Name) := do
  let env ← getEnv
  for h in kernelFactExt.getState env do
    let some (.thmInfo t) := env.find? h | continue
    if t.type == p then return some h
    if ← withReducible (withNewMCtxDepth (isDefEq t.type p)) then return some h
  return none

structure RebuildState where
  memo : Std.HashMap Name (Option Name) := {}
  /-- Native facts proved only through the accessibility-generator route (Lean ≤ 4.36). -/
  viaAcc : Nat := 0
  /-- Native axioms replaced, with the kernel time in ms. -/
  replaced : Array (Name × Nat) := #[]
  /-- Lemmas and definitions rebuilt. -/
  rebuilt : Array Name := #[]
  /-- Kernel-reducible copies created for the evaluations. -/
  copies : Nat := 0
  /-- Kernel declarations (pieces) of the last structured check. -/
  pieces : Nat := 0

abbrev RebuildM := StateRefT RebuildState MetaM

/-- Prefix of rebuilt declarations; distinct from the prefix of kernel-reducible copies, since a
definition can need both. -/
def rebuildPrefix : CoreM Name := return `_ktr ++ (← getEnv).mainModule

/-- Kernel proof of `e = b` for `b` the literal `true`. -/
def proveEqTrue (cfg : KernelConfig) (e : Expr) (name : Name) (lvls : List Name)
    (native? : Option Bool := none) : RebuildM Name := do
  if (← getEnv).contains name then return name
  let r ← proveTrueSplit e name lvls cfg native?
  modify fun s => { s with copies := s.copies + r.copies.size,
                           viaAcc := s.viaAcc + (if r.viaAcc then 1 else 0), pieces := r.pieces }
  return r.thm

mutual

/-- Replace the native axiom `ax : e = true` by a kernel proof of `e = true`. Nested facts: the
definitions in `e` that carry native proofs themselves (e.g. a structure with a `native_decide`
field) are rebuilt first, and the kernel proves `e' = true` for `e'` over the rebuilt definitions,
which is definitionally equal to `e = true` (proof irrelevance). -/
partial def proveNativeAxiom (cfg : KernelConfig) (ax : Name) (info : AxiomVal) :
    RebuildM Name := do
  -- already proved in an imported module (or earlier in this one)?
  if let some thm := (nativeProofExt.getState (← getEnv)).find? ax then
    if (← getEnv).contains thm then
      modify fun s => { s with replaced := s.replaced.push (ax, 0) }
      return thm
  let some (_, e, rhs) := info.type.eq?
    | throwError "kernelize: native axiom `{ax}` does not state an equation:{indentExpr info.type}"
  unless rhs.isConstOf ``Bool.true do
    throwError "kernelize: native axiom `{ax}` is not of the form `e = true`:{indentExpr info.type}"
  let tn ← IO.monoMsNow
  if cfg.trace then eprintRaw s!"NT start {ax}"
  let mut subst : NameMap Name := {}
  for dep in e.getUsedConstants do
    if !subst.contains dep then
      if let some dep' ← rebuild cfg dep then subst := subst.insert dep dep'
  let e := substConsts subst e
  if cfg.shards > 0 && !subst.isEmpty then
    throwError "kernelize: sharding needs a statement without nested native facts; `{ax}` mentions \
      {subst.size} definition(s) that carry native proofs"
  if cfg.trace then
    eprintRaw s!"NT nested {ax} ms={(← IO.monoMsNow) - tn} rebuilt_defs={subst.size} \
      visited={(← get).memo.size}"
  -- `_native` → `_kernel`, so that scans for native axioms do not match the replacement
  -- sharded checks: module-independent names, so pieces proved in separate modules fit together
  let pre ← if cfg.shards > 0 then pure `_ktshard else rebuildPrefix
  let name := ax.components.foldl (init := pre) fun acc c =>
    acc ++ (if c == `_native then `_kernel else c)
  -- a registered proof of the decided proposition (`@[kernel_fact]`): no evaluation
  if e.isAppOfArity ``Decidable.decide 2 && info.levelParams.isEmpty then
    let p := e.getArg! 0
    if let some h ← findKernelFact? p then
      let pf := mkApp3 (mkConst ``decide_eq_true) p (e.getArg! 1) (mkConst h)
      unless (← getEnv).contains name do
        addDeclSync <| .thmDecl
          { name, levelParams := [], type := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e
              (mkConst ``Bool.true), value := pf }
      let bad := (← collectAxioms name).filter (!stdAxioms.contains ·)
      unless bad.isEmpty do
        throwError "kernelize: the @[kernel_fact] proof `{h}` of `{ax}` uses non-standard axioms {bad.toList}"
      if cfg.trace then eprintRaw s!"NT kernel_fact {ax} via {h}"
      modify fun s => { s with replaced := s.replaced.push (ax, 0) }
      if (← getEnv).asyncPrefix?.isNone then
        modifyEnv (nativeProofExt.addEntry · (ax, name))
      return name
  let t0 ← IO.monoMsNow
  -- the axiom exists because compiled evaluation returned `true`
  let thm ← try proveEqTrue cfg e name info.levelParams (native? := some true) catch ex =>
    throwError m!"kernelize: cannot prove the statement of `{ax}` in the kernel:{indentExpr info.type}\n\n{ex.toMessageData}"
  let dt := (← IO.monoMsNow) - t0
  modify fun s => { s with replaced := s.replaced.push (ax, dt) }
  -- one piece of a sharded check: nothing to register
  if cfg.shards > 0 && cfg.shardOnly > 0 then return name
  if (← getEnv).asyncPrefix?.isNone then
    modifyEnv (nativeProofExt.addEntry · (ax, thm))
  return thm

/-- If constant `c` depends on a native axiom, return a rebuilt copy that does not. -/
partial def rebuild (cfg : KernelConfig) (c : Name) : RebuildM (Option Name) := do
  if let some r := (← get).memo[c]? then return r
  let env ← getEnv
  let r ← match env.find? c with
    | some (.axiomInfo info) =>
      if isNativeAxiom env c then some <$> proveNativeAxiom cfg c info else pure none
    | some (.thmInfo t) =>
      rebuildDecl cfg c t.type t.value fun name type value =>
        .thmDecl { name, levelParams := t.levelParams, type, value }
    | some (.defnInfo d) =>
      rebuildDecl cfg c d.type d.value fun name type value =>
        .defnDecl { d with name, type, value, all := [name] }
    | some (.opaqueInfo o) =>
      rebuildDecl cfg c o.type o.value fun name type value =>
        .opaqueDecl { o with name, type, value, all := [name] }
    | _ => pure none
  modify fun s => { s with memo := s.memo.insert c r }
  return r

/-- Rebuild a declaration whose type or value depends on native axioms. -/
partial def rebuildDecl (cfg : KernelConfig) (c : Name) (type value : Expr)
    (mk : Name → Expr → Expr → Declaration) : RebuildM (Option Name) := do
  let value' ← replaceOfReduceBool cfg c value
  let mut subst : NameMap Name := {}
  for dep in type.getUsedConstants ++ value'.getUsedConstants do
    if !subst.contains dep then
      if let some dep' ← rebuild cfg dep then subst := subst.insert dep dep'
  if subst.isEmpty && value' == value then return none
  let value := value'
  let name := (← rebuildPrefix) ++ c
  unless (← getEnv).contains name do
    addDeclSync (mk name (substConsts subst type) (substConsts subst value))
    modify fun s => { s with rebuilt := s.rebuilt.push c }
  return some name

/-- Older toolchains: replace `Lean.ofReduceBool a true h` by a kernel proof of `a = true`. -/
partial def replaceOfReduceBool (cfg : KernelConfig) (c : Name) (value : Expr) : RebuildM Expr := do
  unless (value.find? (·.isConstOf `Lean.ofReduceBool)).isSome do return value
  let mut value := value
  let mut i := 0
  while true do
    let some app := value.find? (·.isAppOfArity `Lean.ofReduceBool 3) | break
    let a := app.getArg! 0
    unless app.getArg! 1 |>.isConstOf ``Bool.true do
      throwError "kernelize: `Lean.ofReduceBool` with a right-hand side other than `true` in `{c}`"
    let lvls := (collectLevelParams {} a).params.toList
    let thm ← proveEqTrue cfg a ((← rebuildPrefix) ++ c ++ (`ofReduceBool).appendIndexAfter i)
      lvls
    modify fun s => { s with replaced := s.replaced.push (`Lean.ofReduceBool, 0) }
    value := value.replace fun e => if e == app then some (mkConst thm (lvls.map mkLevelParam)) else none
    i := i + 1
  return value

end

/-- The statement for `T.kernel`, given `T`'s statement `type` and the rebuilt proof `src'`: `type`
itself, or, when `type` mentions definitions that carry native proofs (a structure with a
`native_decide` field, say), `type` over their rebuilt copies, which is definitionally equal to
`type` by proof irrelevance (a statement that mentions such a definition depends on its native
axiom). Also returns the definitions replaced. -/
def rebuiltStatement (type : Expr) (src' : Name) : CoreM (Expr × Array Name) := do
  let some info := (← getEnv).find? src' | return (type, #[])
  if info.type == type then return (type, #[])
  let used := info.type.getUsedConstants
  return (info.type, type.getUsedConstants.filter (!used.contains ·))

/-- Note appended to reports when the statement is over rebuilt definitions. -/
def stmtNote (stmtRebuilt : Array Name) : String :=
  if stmtRebuilt.isEmpty then "" else
    s!"\nThe statement mentions definitions that carry native proofs; it is stated over their \
      rebuilt copies (definitionally equal by proof irrelevance): {stmtRebuilt.toList}"

declare_command_config_elab elabKernelizeConfig KernelConfig

/-- `kernelize T` adds `T.kernel`, a proof of `T`'s statement in which every axiom added by
`native_decide`/`bv_decide` is replaced by a proof that Lean's kernel checks by evaluation.
`kernelize T as T'` chooses the name. The result is checked to depend on no axiom beyond
`propext`, `Classical.choice` and `Quot.sound`. -/
syntax (name := kernelizeCmd) "kernelize " ident (" as " ident)? Lean.Parser.Tactic.optConfig :
  command

@[command_elab kernelizeCmd] def elabKernelize : CommandElab := fun stx => do
  let cfg ← elabKernelizeConfig stx[3]
  let cfg := { cfg with native := false }
  liftTermElabM do
    let src ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let dst := if stx[2].isNone then src ++ `kernel else stx[2][1].getId
    let some info := (← getEnv).find? src | throwError "unknown constant `{src}`"
    let t0 ← IO.monoMsNow
    let (r, s) ← (rebuild cfg src).run {}
    let some src' := r
      | throwError "kernelize: `{src}` does not depend on any `native_decide`/`bv_decide` axiom"
    -- the statement is `src`'s statement, expression for expression, unless it mentions
    -- definitions that carry native proofs: then it is stated over their rebuilt copies
    let (type, stmtRebuilt) ← rebuiltStatement info.type src'
    let us := info.levelParams.map mkLevelParam
    addDeclSync <| .thmDecl
      { name := dst, levelParams := info.levelParams, type, value := mkConst src' us }
    let axs ← collectAxioms dst
    let bad := axs.filter (!stdAxioms.contains ·)
    unless bad.isEmpty do
      throwError "kernelize: `{dst}` still depends on non-standard axioms {bad.toList}"
    let ms := (← IO.monoMsNow) - t0
    let kms := s.replaced.foldl (· + ·.2) 0
    logInfo m!"kernelize: `{dst}` proves the statement of `{src}` with axioms {axs.toList}.\n\
      Replaced {s.replaced.size} native axiom(s) by kernel proofs ({kms} ms of kernel \
      evaluation); rebuilt {s.rebuilt.size} lemma(s)/definition(s); created {s.copies} \
      kernel-reducible copies; {ms} ms in total.{stmtNote stmtRebuilt}"

/-- Re-prove one theorem (the body of `kernelize`); returns a one-line report. Errors are
reported, not thrown, when `soft`. -/
def kernelizeOne (cfg : KernelConfig) (src dst : Name) (soft : Bool := false) : TermElabM String := do
  let some info := (← getEnv).find? src | throwError "unknown constant `{src}`"
  let t0 ← IO.monoMsNow
  let envBefore ← getEnv
  try
    let (r, s) ← (rebuild cfg src).run {}
    let some src' := r
      | throwError "`{src}` does not depend on any native_decide/bv_decide axiom"
    let (type, stmtRebuilt) ← rebuiltStatement info.type src'
    let us := info.levelParams.map mkLevelParam
    addDeclSync <| .thmDecl
      { name := dst, levelParams := info.levelParams, type, value := mkConst src' us }
    let axs ← collectAxioms dst
    let bad := axs.filter (!stdAxioms.contains ·)
    unless bad.isEmpty do
      throwError "`{dst}` still depends on non-standard axioms {bad.toList}"
    let kms := s.replaced.foldl (· + ·.2) 0
    return s!"OK\t{src}\t{dst}\taxioms={axs.toList}\tnative_axioms={s.replaced.size}\t\
      kernel_ms={kms}\trebuilt={s.rebuilt.size}\tcopies={s.copies}\ttotal_ms={(← IO.monoMsNow) - t0}\
      \tacc_fallback={s.viaAcc}\
      {if stmtRebuilt.isEmpty then "" else s!"\tstatement_rebuilt={stmtRebuilt.toList}"}"
  catch ex =>
    unless soft do throw ex
    setEnv envBefore
    let msg := (← ex.toMessageData.toString).replace "\n" " "
    return s!"FAIL\t{src}\t{dst}\t{msg.take 2000}"

/-- Native axioms that constant `c` depends on (through any chain of declarations). -/
def nativeAxiomsOf (c : Name) : CoreM (Array Name) := do
  let env ← getEnv
  return (← collectAxioms c).filter (isNativeAxiom env)

/-- `#kernel_blockers T` reports, without evaluating anything, whether the kernel can evaluate
each `native_decide`/`bv_decide` fact that `T` depends on: the number of kernel-reducible copies
needed, and every reachable constant without a kernel definition, with the path to it. -/
syntax (name := kernelBlockersCmd) "#kernel_blockers " ident : command

/-- Also print the reports of `#kernel_blockers` and `trust_check` to standard error as soon as
they are made (drivers keep them even when the process is stopped later). -/
register_option nativeTrust.eprint : Bool := {
  defValue := false
  descr := "NativeTrust: also print #kernel_blockers/trust_check reports to standard error"
}

/-- `logInfo`, and with `nativeTrust.eprint` also the process's standard error at once. -/
def report (msg : MessageData) : CoreM Unit := do
  logInfo msg
  if nativeTrust.eprint.get (← getOptions) then
    eprintRaw ((← msg.toString).replace "\n" "\n  ")

/-- The report of `#kernel_blockers` on constant `src`, as an info message. Static: nothing is
evaluated and no copy is built (well-founded recursion and registered replacements are followed as
the copies would have them). -/
def kernelBlockersCore (src : Name) : TermElabM Unit := do
  let axs ← nativeAxiomsOf src
  if axs.isEmpty then
    report m!"`{src}` does not depend on any native_decide/bv_decide axiom"
    return
  let mut msgs := #[]
  for ax in axs do
    let some (.axiomInfo info) := (← getEnv).find? ax | continue
    let some (_, e, _) := info.type.eq? | continue
    let blockers ← findBlockers e (static := true)
    msgs := msgs.push <| if blockers.isEmpty then
        m!"`{ax}`: no blocker"
      else
        m!"`{ax}`: blockers:\n" ++
          MessageData.joinSep (blockers.toList.map Blocker.toMessageData) "\n"
  report (MessageData.joinSep msgs.toList "\n")

@[command_elab kernelBlockersCmd] def elabKernelBlockers : CommandElab := fun stx =>
  liftTermElabM do kernelBlockersCore (← realizeGlobalConstNoOverloadWithInfo stx[1])

/-- `kernelize_module M` runs `kernelize` on every theorem of the imported module `M` that
depends on a `native_decide`/`bv_decide` axiom (adding `T.kernel` for each) and prints one
tab-separated line per theorem: `OK`/`FAIL`, names, axioms, kernel time. Failures do not stop
the others. -/
syntax (name := kernelizeModuleCmd) "kernelize_module " ident Lean.Parser.Tactic.optConfig :
  command

@[command_elab kernelizeModuleCmd] def elabKernelizeModule : CommandElab := fun stx => do
  let cfg ← elabKernelizeConfig stx[2]
  let cfg := { cfg with native := false }
  let mod := stx[1].getId
  liftTermElabM do
    let env ← getEnv
    let some idx := env.getModuleIdx? mod | throwError "module `{mod}` is not imported"
    let names := env.header.moduleData[idx.toNat]!.constNames
    let mut lines := #[]
    for n in names do
      let some (.thmInfo _) := env.find? n | continue
      if n.isInternal then continue
      if (← nativeAxiomsOfCore n).isEmpty then continue
      lines := lines.push (← kernelizeOne cfg n (n ++ `kernel) (soft := true))
    let ok := lines.filter (·.startsWith "OK") |>.size
    logInfo m!"kernelize_module {mod}: {ok}/{lines.size} theorems re-proved\n{"\n".intercalate lines.toList}"

/-- `trust_check T` gives a verdict on theorem `T`:
* `CLEAN`: `T` depends only on `propext`, `Classical.choice`, `Quot.sound`;
* `KERNELIZED`: `T` depended on `native_decide`/`bv_decide` axioms, and `T.kernel` (same
  statement) now depends only on the standard axioms;
* `REJECTED`: `T` depends on another non-standard axiom (e.g. `sorryAx`, a custom axiom), or a
  native fact could not be re-proved in the kernel; the reason follows (false in the logic, with
  the compiled-code sources such as `@[csimp]` lemmas resting on hidden axioms; a blocking
  constant; or resources). -/
syntax (name := trustCheckCmd) "trust_check " ident Lean.Parser.Tactic.optConfig : command

/-- The verdict of `trust_check` on theorem `src`, as an info message. -/
def trustCheckCore (cfg : KernelConfig) (src : Name) : TermElabM Unit := do
  let env ← getEnv
  let axs ← collectAxioms src
  let natives := axs.filter fun a => isNativeAxiom env a || isLegacyNativeAxiom a
  let others := axs.filter fun a =>
    !stdAxioms.contains a && !isNativeAxiom env a && !isLegacyNativeAxiom a
  if !others.isEmpty then
    report m!"REJECTED `{src}`: depends on non-standard axioms {others.toList}"
  else if natives.isEmpty then
    report m!"CLEAN `{src}`: axioms {axs.toList}"
  else
    let line ← kernelizeOne cfg src (src ++ `kernel) (soft := true)
    if line.startsWith "OK" then
      report m!"KERNELIZED `{src}` as `{src ++ `kernel}` ({natives.size} native axiom(s) replaced)\n{line}"
    else
      report m!"REJECTED `{src}`: a native fact could not be re-proved in the kernel\n{line}"

@[command_elab trustCheckCmd] def elabTrustCheck : CommandElab := fun stx => do
  let cfg ← elabKernelizeConfig stx[2]
  let cfg := { cfg with native := false }
  liftTermElabM do
    trustCheckCore cfg (← realizeGlobalConstNoOverloadWithInfo stx[1])

/-- `#kernel_blockers_const f g …` reports the constants without a kernel definition that are
reachable from the definitions `f`, `g`, … (no evaluation, no theorem needed): a quick check of
whether a checker function can ever be evaluated by the kernel. -/
syntax (name := kernelBlockersConstCmd) "#kernel_blockers_const " (ppSpace ident)+ : command

@[command_elab kernelBlockersConstCmd] def elabKernelBlockersConst : CommandElab := fun stx =>
  liftTermElabM do
    let mut msgs := #[]
    for id in stx[1].getArgs do
      let c ← realizeGlobalConstNoOverloadWithInfo id
      let blockers ← findBlockers (mkConst c) (static := true)
      msgs := msgs.push <| if blockers.isEmpty then
          m!"`{c}`: no blocker"
        else
          m!"`{c}`: blockers:\n" ++
            MessageData.joinSep (blockers.toList.map Blocker.toMessageData) "\n"
    logInfo (MessageData.joinSep msgs.toList "\n")

/-- `#native_facts T` prints one line per `native_decide`/`bv_decide` axiom that `T` depends on:
the declaration that used the tactic, the module defining it, and whether a kernel proof of the
fact is already registered (imported). Used by drivers that kernelize facts in parallel. -/
syntax (name := nativeFactsCmd) "#native_facts " ident : command

@[command_elab nativeFactsCmd] def elabNativeFacts : CommandElab := fun stx =>
  liftTermElabM do
    let src ← realizeGlobalConstNoOverloadWithInfo stx[1]
    let env ← getEnv
    let reg := nativeProofExt.getState env
    let mut lines := #[]
    for ax in ← nativeAxiomsOfCore src do
      -- `<decl>._native.<tactic>.ax…` → `<decl>`
      let decl := ((privateToUserName ax).components.takeWhile (· != `_native)).foldl (· ++ ·)
        Name.anonymous
      let mod := match env.getModuleIdxFor? ax with
        | some idx => toString env.header.moduleNames[idx.toNat]!
        | none => "<current>"
      lines := lines.push s!"FACT\t{decl}\t{mod}\t{if reg.contains ax then "proved" else "native"}"
    logInfo m!"{lines.size} native facts behind `{src}`\n{"\n".intercalate lines.toList}"

/-- Theorems of the imported module `mod` that depend on a `native_decide`/`bv_decide` axiom, in
declaration order: the name, the native axioms referenced by the theorem's own proof term (direct
uses; robust to the private names that module-system files give these axioms), and the number of
native axioms it depends on. Internal theorems (private, `_proof_i`) are kept when they use the
tactic directly. -/
def nativeTheoremsOf (mod : Name) : CoreM (Array (Name × Array Name × Nat)) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod | throwError "module `{mod}` is not imported"
  let mut out := #[]
  for n in env.header.moduleData[idx.toNat]!.constNames do
    let some (.thmInfo t) := env.find? n | continue
    let axs ← nativeAxiomsOfCore n
    if axs.isEmpty then continue
    let direct := axs.filter fun ax => (t.value.find? (·.isConstOf ax)).isSome
    if n.isInternal && direct.isEmpty then continue
    out := out.push (n, direct, axs.size)
  return out

/-- `#native_theorems M` prints `THM <name> <direct native facts> <all native facts> <index>` for
every theorem of the imported module `M` that depends on a `native_decide`/`bv_decide` axiom
(drivers run `trust_check_nth M <index>` on each in its own process, with its own time and memory
limits; the index also reaches private theorems, which have no name to write). -/
syntax (name := nativeTheoremsCmd) "#native_theorems " ident : command

@[command_elab nativeTheoremsCmd] def elabNativeTheorems : CommandElab := fun stx =>
  liftTermElabM do
    let mod := stx[1].getId
    let thms ← nativeTheoremsOf mod
    let lines := thms.mapIdx fun i (n, direct, all) => s!"THM\t{n}\t{direct.size}\t{all}\t{i}"
    logInfo m!"{lines.size} native theorems in `{mod}`\n{"\n".intercalate lines.toList}"

/-- The `i`-th theorem listed by `#native_theorems M`. -/
def nthNativeTheorem (mod : Name) (i : Nat) : CoreM Name := do
  let thms ← nativeTheoremsOf mod
  let some (n, _) := thms[i]? | throwError "`{mod}` has {thms.size} native theorems, no index {i}"
  return n

/-- `trust_check_nth M i` is `trust_check` on the `i`-th theorem listed by `#native_theorems M`. -/
syntax (name := trustCheckNthCmd) "trust_check_nth " ident num Lean.Parser.Tactic.optConfig :
  command

@[command_elab trustCheckNthCmd] def elabTrustCheckNth : CommandElab := fun stx => do
  let cfg ← elabKernelizeConfig stx[3]
  let cfg := { cfg with native := false }
  liftTermElabM do
    trustCheckCore cfg (← nthNativeTheorem stx[1].getId stx[2].isNatLit?.get!)

/-- `#kernel_blockers_nth M i` is `#kernel_blockers` on the `i`-th theorem listed by
`#native_theorems M`. -/
syntax (name := kernelBlockersNthCmd) "#kernel_blockers_nth " ident num : command

@[command_elab kernelBlockersNthCmd] def elabKernelBlockersNth : CommandElab := fun stx =>
  liftTermElabM do
    kernelBlockersCore (← nthNativeTheorem stx[1].getId stx[2].isNatLit?.get!)

/-- Native axioms declared in the imported module `mod`, in declaration order: the axiom, the
tactic that made it, and whether the declaration that used the tactic is a definition or an
instance (a fact inside data or behind an instance argument, e.g. `Fact (Nat.Prime p)`, that other
facts' statements can mention). -/
def nativeAxiomsIn (mod : Name) : CoreM (Array (Name × Name × Bool)) := do
  let env ← getEnv
  let some idx := env.getModuleIdx? mod | throwError "module `{mod}` is not imported"
  let mut out := #[]
  for n in env.header.moduleData[idx.toNat]!.constNames do
    unless isNativeAxiom env n do continue
    let cs := n.components
    let decl := (cs.takeWhile (· != `_native)).foldl (· ++ ·) Name.anonymous
    let tac := (cs.dropWhile (· != `_native)).drop 1 |>.headD .anonymous
    -- abstracted proofs of a definition: `<def>._proof_i` (theorem) inside `<def>`
    -- definitions and instances (also instances of `Prop` classes such as `Fact`, which are
    -- theorems): other facts' statements can mention them
    let isDef (d : Name) : Bool := Meta.isInstanceCore env d || match env.find? d with
      | some (.defnInfo _) => true
      | some (.thmInfo _) =>
        match d with
        | .str p s => s.startsWith "_proof" && (env.find? p matches some (.defnInfo _))
        | _ => false
      | _ => false
    -- module-system files give the axiom a private name even when the declaration is public
    let declDef := isDef decl || isDef (privateToUserName decl)
    out := out.push (n, tac, declDef)
  return out

/-- `#native_axioms M` prints `AX <axiom> <tactic> <inner> <index>` for every `native_decide`/
`bv_decide` axiom declared in the imported module `M` (`inner`: the tactic was used inside a
definition). Drivers prove each with `prove_native_axiom_nth M <index>` in its own process. -/
syntax (name := nativeAxiomsCmd) "#native_axioms " ident : command

@[command_elab nativeAxiomsCmd] def elabNativeAxioms : CommandElab := fun stx =>
  liftTermElabM do
    let mod := stx[1].getId
    let axs ← nativeAxiomsIn mod
    let lines := axs.mapIdx fun i (n, tac, inner) => s!"AX\t{n}\t{tac}\t{inner}\t{i}"
    logInfo m!"{lines.size} native axioms in `{mod}`\n{"\n".intercalate lines.toList}"

/-- `prove_native_axiom_nth M i` proves the statement of the `i`-th axiom listed by
`#native_axioms M` by kernel evaluation (definitions in it that carry native proofs are rebuilt
first) and registers the proof, so that modules importing this one reuse it (`kernelize`,
`trust_check`, and other facts whose statements mention it). Reports `PROVED <axiom>` with the
kernel time, or `FAILED <axiom>` with the reason. -/
syntax (name := proveNativeAxiomNthCmd) "prove_native_axiom_nth " ident num
  Lean.Parser.Tactic.optConfig : command

@[command_elab proveNativeAxiomNthCmd] def elabProveNativeAxiomNth : CommandElab := fun stx => do
  let cfg ← elabKernelizeConfig stx[3]
  let cfg := { cfg with native := false }
  liftTermElabM do
    let mod := stx[1].getId
    let i := stx[2].isNatLit?.get!
    let axs ← nativeAxiomsIn mod
    let some (ax, _, _) := axs[i]? | throwError "`{mod}` has {axs.size} native axioms, no index {i}"
    let some (.axiomInfo info) := (← getEnv).find? ax | throwError "unknown axiom `{ax}`"
    let envBefore ← getEnv
    let t0 ← IO.monoMsNow
    try
      let (thm, s) ← (proveNativeAxiom cfg ax info).run {}
      let kms := s.replaced.foldl (· + ·.2) 0
      if cfg.shards > 0 && cfg.shardOnly > 0 then
        report m!"SHARD {cfg.shardOnly - 1}/{s.pieces} `{ax}`: \
          {if cfg.shardOnly ≤ s.pieces then "PIECE_PROVED" else "NO_SUCH_PIECE"} kernel_ms={kms} \
          copies={s.copies} total_ms={(← IO.monoMsNow) - t0}"
        return
      report m!"PROVED `{ax}` as `{thm}`: kernel_ms={kms} native_axioms={s.replaced.size} \
        rebuilt={s.rebuilt.size} copies={s.copies} total_ms={(← IO.monoMsNow) - t0} \
        acc_fallback={s.viaAcc} pieces={s.pieces}"
    catch ex =>
      setEnv envBefore
      report m!"FAILED `{ax}`: {ex.toMessageData}"

end NativeTrust
