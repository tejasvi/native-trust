import Lean
import NativeTrust.Copy
import NativeTrust.CSimpCompat

/-!
# Proving `e = true` by kernel evaluation

`proveTrueByKernel e name` adds a theorem `name : e = true` for a closed `Bool` term `e`. The
kernel itself evaluates `e`, after `kernelCopy` has made the reachable definitions
kernel-reducible:

* `name.eval : e' = true := Eq.refl true` (the kernel reduces `e'` to `true`), and
* `name : e = true := Eq.trans (Eq.refl e) name.eval` (the kernel checks `e ≡ e'` by unfolding
  and proof irrelevance).

Nothing from compiled code enters the proof. Compiled evaluation (`nativeEval`) is used only as
an untrusted oracle: to fail fast on false propositions and to explain disagreements.

When the kernel cannot finish, `diagnose` reports whether the kernel reduced `e'` to `false`
(then the native result came from an implementation that differs from the logical definition,
or from platform-dependent behaviour) or got stuck, and lists the constants without a
kernel-usable definition (`partial` functions, opaque primitives, axioms) reachable from `e'`,
each with the path of definitions that leads to it.
-/

open Lean Meta

namespace NativeTrust

/-- The axioms of Lean's standard foundations. -/
def stdAxioms : List Name := [``propext, ``Classical.choice, ``Quot.sound]

structure KernelConfig where
  /-- Heartbeat limit (in thousands, like `maxHeartbeats`) for the kernel evaluation;
  `0` means no limit. -/
  maxHeartbeats : Nat := 0
  /-- `maxRecDepth` for the kernel evaluation. -/
  maxRecDepth : Nat := 100000
  /-- Run the compiled evaluator first, as an untrusted oracle, to fail fast. -/
  native : Bool := true
  /-- Make well-founded recursion kernel-reducible (`kernelCopy`), with the fuel version
  `fixFuel` (durable) or, with `wfAcc`, the accessibility generator (Lean ≤ 4.36). -/
  wf : Bool := true
  wfAcc : Bool := false
  /-- If the fuel route leaves well-founded recursion unbridged (a copy whose equation congruence
  cannot prove), retry with the accessibility-generator route; recorded in the result
  (`viaAcc`), since that route needs Lean ≤ 4.36. -/
  accFallback : Bool := true
  /-- Passed to the copier (`CopyConfig.skipUnchanged`). -/
  skipUnchanged : Bool := false
  /-- Passed to the copier (`CopyConfig.transport`); set by the fuel route's retry. -/
  transport : Bool := false
  /-- Experimental: also copy all reachable definitions with small definitions inlined (up to
  2.5x faster kernel evaluation on `Nat`/`List` code, but proving the copies equal to the
  originals can be slow when their bodies contain closed computations; see `NativeTrust.Copy`). -/
  opt : Bool := false
  /-- On failure, also ask the kernel whether the term reduces to `false`
  (costs a second evaluation). -/
  diagnoseFalse : Bool := true
  /-- Split the check into up to this many kernel declarations, along `&&` and along
  `List.all l f` for an explicit list `l` (see `proveTrueSplit`). Each declaration has its own
  kernel caches, so this bounds memory; `1` = no splitting. -/
  split : Nat := 1
  /-- Heartbeat limit (in thousands) for the kernel evaluation when constants without a kernel
  definition (`partial` functions, C primitives, opaque constants, …) are reachable from the term:
  evaluation usually gets stuck at one of them, and a stuck evaluation can exhaust memory before it
  fails. Applies only when `maxHeartbeats` is `0` or larger; `0` = no limit. -/
  blockedHeartbeats : Nat := 50000
  /-- Print the phases (copies, evaluation) with their times to standard error as they end
  (drivers keep them even when a check is stopped). -/
  trace : Bool := false
  deriving Inhabited

def mkBoolEq (e b : Expr) : Expr := mkApp3 (mkConst ``Eq [1]) (mkConst ``Bool) e b
def boolTrue : Expr := mkConst ``Bool.true
def boolFalse : Expr := mkConst ``Bool.false
def reflBool (b : Expr) : Expr := mkApp2 (mkConst ``Eq.refl [1]) (mkConst ``Bool) b

/-- Add a theorem, checked synchronously by the kernel, and return the time it took in ms. On
failure the environment is restored: `Lean.addDecl` would otherwise leave the failed declaration
behind as an axiom. -/
def tryAddTheorem (name : Name) (lvls : List Name) (type value : Expr) (cfg : KernelConfig) :
    CoreM (Except Exception Nat) := do
  let env ← getEnv
  let t0 ← IO.monoMsNow
  try
    withOptions (fun o => maxRecDepth.set (maxHeartbeats.set (Elab.async.set o false)
        cfg.maxHeartbeats) cfg.maxRecDepth) do
      addDecl (.thmDecl { name, levelParams := lvls, type, value })
    return .ok ((← IO.monoMsNow) - t0)
  catch ex =>
    setEnv env
    return .error ex

/-- Evaluate a closed `Bool` term with compiled code, as `native_decide` does, but without adding
any axiom. Untrusted: used only to fail fast and to explain disagreements. -/
def nativeEval (e : Expr) : MetaM (Except MessageData Bool) := do
  let levels := (collectLevelParams {} e).params.toList
  withoutModifyingEnv do
    let auxName ← mkAuxDeclName `_kt_native
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := levels, type := mkConst ``Bool, value := e,
      hints := .abbrev, safety := .safe }
    modifyEnv (markMeta · auxName)
    try
      -- raw option names: these options do not exist on older toolchains (then ignored)
      withOptions (fun o => ((Elab.async.set o false).insert `compiler.postponeCompile (.ofBool false)).insert
          `compiler.relaxedMetaCheck (.ofBool true)) do
        addAndCompile decl
    catch ex => return .error m!"compilation failed: {ex.toMessageData}"
    try
      return .ok (← unsafe evalConst Bool auxName)
    catch ex => return .error m!"evaluation failed: {ex.toMessageData}"

/-- Evaluate a closed `Nat` term with compiled code. Untrusted: used only as a hint (e.g. the
length of a list to split), never in a proof. -/
def nativeEvalNat (e : Expr) : MetaM (Except MessageData Nat) := do
  let levels := (collectLevelParams {} e).params.toList
  withoutModifyingEnv do
    let auxName ← mkAuxDeclName `_kt_native_nat
    let decl := Declaration.defnDecl {
      name := auxName, levelParams := levels, type := mkConst ``Nat, value := e,
      hints := .abbrev, safety := .safe }
    modifyEnv (markMeta · auxName)
    try
      -- raw option names: these options do not exist on older toolchains (then ignored)
      withOptions (fun o => ((Elab.async.set o false).insert `compiler.postponeCompile (.ofBool false)).insert
          `compiler.relaxedMetaCheck (.ofBool true)) do
        addAndCompile decl
    catch ex => return .error m!"compilation failed: {ex.toMessageData}"
    try
      return .ok (← unsafe evalConst Nat auxName)
    catch ex => return .error m!"evaluation failed: {ex.toMessageData}"

/-! ## Blockers -/

/-- A constant reachable from the evaluated term that the kernel cannot unfold. -/
structure Blocker where
  name : Name
  reason : String
  /-- Definitions leading from the root to the blocker. -/
  path : List Name

def blockerReason (env : Environment) (n : Name) : Option String :=
  if n == `WellFounded.extrinsicFix || n == `WellFounded.extrinsicFix₂ ||
      n == `WellFounded.extrinsicFix₃ then
    some "loop with extrinsic termination (`WellFounded.extrinsicFix`, used by iterators: \
      `Std.Iter` loops, polymorphic ranges `a...b`, `String.Slice` functions such as \
      `String.toNat?`): its value depends on a classical test of well-foundedness, which the \
      kernel cannot evaluate. Not supported yet; loops over `[a:b]`, `List` or `Array` work"
  else if n == ``WellFounded.fix then
    some "well-founded recursion (`WellFounded.fix`, used for non-`Nat` termination measures, \
      e.g. lexicographic ones): the kernel can evaluate it only by reducing the \
      well-foundedness proof, which Lean blocks (`Lean.opaqueId`) and which from Lean 4.37 on \
      never reduces. Remedies: a `Nat`-valued `termination_by` (Lean then compiles the \
      recursion to fuel), or a proved fuel version registered with `@[kernel_replace]`; on \
      Lean ≤ 4.36 NativeTrust's `wf` transform also works"
  else if n == `Lean.Order.fix then
    some "fixpoint definition (`partial_fixpoint`, `Lean.Order.fix`): defined through \
      `Classical.choice` (least upper bounds of a chain), so the kernel cannot evaluate it; the \
      fixpoint equation holds as a theorem, so a `@[kernel_replace]` fuel version can be proved \
      equal to it"
  else if n == ``Lean.Loop.forIn then
    some "`while`/`repeat` loop: implemented by a `partial` function, so in the logic its \
      result is unspecified and no statement about it can be proved; a total version \
      (structural recursion, `termination_by`, or fuel) is needed"
  else
  match env.find? n with
  | some (.opaqueInfo _) =>
    if n == ``System.Platform.getNumBits then
      some "platform word size: `USize` arithmetic (used by `HashMap`, `HashSet`, `Array.uget`, …) \
        has no kernel value, and results may differ between 32- and 64-bit platforms"
    else if n == ``Lean.opaqueId then
      some "`Lean.opaqueId` blocks reduction on purpose"
    else if env.contains (Compiler.mkUnsafeRecName n) then
      some "`partial` function: in the logic it is an opaque constant with no equations, so \
        no statement about its result can be proved (this includes `while`/`repeat` loops); \
        a total version (structural, `termination_by`, or fuel) is needed"
    else match Compiler.getImplementedBy? env n with
      | some impl => some s!"opaque constant implemented by `{impl}`"
      | none =>
        if isExtern env n then some "primitive implemented in C (`@[extern]`) with no definition"
        else some "opaque constant"
  | some (.axiomInfo _) =>
    -- proofs never block evaluation: `propext`, `Quot.sound` (reached through the proof arguments
    -- of `Quot.lift`, `Finset` and `Multiset` operations) and native facts (rebuilt separately)
    if n == ``propext || n == ``Quot.sound || n.components.contains `_native then none
    else some "axiom"
  | some (.defnInfo d) =>
    if d.safety != .safe then some "unsafe or partial definition" else none
  | _ => none

/-- Constants whose bodies the kernel never needs when evaluating a call site: panic messages and
trace messages (their values are discarded by `panicCore` and `dbgTrace` in the logic). -/
def nonEvaluated : List Name :=
  [``mkPanicMessage, ``mkPanicMessageWithDecl, ``dbgTrace, ``dbgTraceIfShared]

/-- The constants of `e` outside the subterms that are syntactically proofs: applications of
theorems, and `Eq.mp`/`Eq.mpr`/`cast` between propositions (the proofs that `transportCopy` keeps as
they are, with the original constants inside). Evaluation never reduces a proof. -/
def relevantConsts (env : Environment) (e : Expr) : Array Name := Id.run do
  let mut out : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  let mut visited : Std.HashSet Expr := {}
  let mut todo : Array Expr := #[e]
  while h : 0 < todo.size do
    let x := todo.back
    todo := todo.pop
    if visited.contains x then continue
    visited := visited.insert x
    match x with
    | .const c _ =>
      unless seen.contains c do
        seen := seen.insert c
        out := out.push c
    | .app .. =>
      let isProofApp := match x.getAppFn with
        | .const c ls => (env.find? c matches some (.thmInfo _)) ||
            ((c == ``Eq.mp || c == ``Eq.mpr || c == ``cast) && ls == [levelZero])
        | _ => false
      unless isProofApp do
        todo := todo.push x.getAppFn
        for a in x.getAppArgs do todo := todo.push a
    | .lam _ t b _ | .forallE _ t b _ => todo := (todo.push t).push b
    | .letE _ t v b _ => todo := ((todo.push t).push v).push b
    | .mdata _ b | .proj _ _ b => todo := todo.push b
    | _ => pure ()
  return out

/-- Constants reachable from `e` through definition bodies that the kernel cannot unfold. With
`static`, `e` is the original term (no `kernelCopy`): well-founded recursion and registered
replacements are followed as the copies would have them, so no copy needs to be built. -/
def findBlockers (e : Expr) (static : Bool := false) (skipProofs : Bool := false) :
    CoreM (Array Blocker) := do
  let env ← getEnv
  let user := kernelReplaceExt.getState env
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  let mut out : Array Blocker := #[]
  for c in e.getUsedConstants do
    unless seen.contains c do
      seen := seen.insert c
      queue := queue.push c
  let mut i := 0
  while h : i < queue.size do
    let c := queue[i]
    i := i + 1
    -- `static`: `e` has not been through `kernelCopy`; follow what the copies would contain
    -- (`WellFounded.fix` ↦ `fixFuel`, registered replacements) instead of building them
    if static then
      if c == ``WellFounded.fix then continue
      if let some (g, _) := user.find? c then
        unless seen.contains g do
          seen := seen.insert g
          parent := parent.insert g c
          queue := queue.push g
        continue
    if let some reason := blockerReason env c then
      let mut path := [c]
      let mut cur := c
      for _ in [0:1000] do
        match parent[cur]? with
        | some p => path := p :: path; cur := p
        | none => break
      out := out.push { name := c, reason, path }
      continue
    -- NativeTrust's own kernel-reducible combinators are leaves
    if c == ``NativeTrust.wfFix || c == ``NativeTrust.accGen || c == ``NativeTrust.fixFuel ||
        c == ``NativeTrust.fixFuelAux then continue
    -- messages that the logic never evaluates: `panicCore msg` is `default` and `dbgTrace msg f`
    -- is `f ()`, and kernel reduction is lazy, so building the message (with the C string
    -- primitives) is never reached, even on a panic path
    if nonEvaluated.contains c then continue
    if let some (.defnInfo d) := env.find? c then
      -- after `kernelCopy` (not `static`), proofs are skipped: transported copies keep the
      -- original constants inside their proofs, which evaluation never reaches
      for dep in (if static || !skipProofs then d.value.getUsedConstants else relevantConsts env d.value) do
        unless seen.contains dep do
          seen := seen.insert dep
          parent := parent.insert dep c
          queue := queue.push dep
  return out

/-- How compiled code can differ from the logical definition of a constant. -/
inductive CompiledSource where
  /-- `@[implemented_by impl]`: no proof relates `impl` to the definition. -/
  | implementedBy (impl : Name)
  /-- `@[csimp] thm : @c = @repl`. `nonStd` are the non-standard axioms `thm` depends on; they
  never show up in `#print axioms` of a `native_decide` theorem (Lean issue #7463). -/
  | csimp (repl thm : Name) (isThm : Bool) (nonStd : Array Name)
  /-- `@[extern]`: compiled code calls a C function. -/
  | extern

/-- Reachable constants whose compiled code is not their logical definition. -/
def findCompiledSources (e : Expr) : CoreM (Array (Name × CompiledSource)) := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut stack := e.getUsedConstants
  let mut out := #[]
  while h : 0 < stack.size do
    let c := stack.back
    stack := stack.pop
    if seen.contains c then continue
    seen := seen.insert c
    if let some impl := Compiler.getImplementedBy? env c then
      out := out.push (c, .implementedBy impl)
    if let some (repl, thm) := csimpEntry? env c then
      let axs ← collectAxioms thm
      let isThm := env.find? thm matches some (.thmInfo _)
      let nonStd := axs.filter (!stdAxioms.contains ·)
      -- replacements proved by a theorem from the standard axioms are not suspects
      if !isThm || !nonStd.isEmpty then
        out := out.push (c, .csimp repl thm isThm nonStd)
    if isExtern env c && !kernelPrimitives.contains c then
      out := out.push (c, .extern)
    if let some (.defnInfo d) := env.find? c then
      stack := stack ++ d.value.getUsedConstants
  return out

def CompiledSource.toMessageData (c : Name) : CompiledSource → MessageData
  | .implementedBy impl => m!"• `{c}` is implemented by `{impl}` (`@[implemented_by]`, no proof)"
  | .csimp repl thm isThm nonStd =>
    let base := m!"• `{c}` is replaced by `{repl}` in compiled code (`@[csimp] {thm}`)"
    let base := if isThm then base else base ++ m!"; `{thm}` is not a theorem"
    if nonStd.isEmpty then base
    else base ++ m!"; `{thm}` depends on the NON-STANDARD axioms {nonStd.toList}, which \
      `#print axioms` does not show for native_decide theorems (Lean issue #7463)"
  | .extern => m!"• `{c}` is `@[extern]`: compiled code calls C, the kernel uses its Lean body"

def Blocker.toMessageData (b : Blocker) : MessageData :=
  let shown := if b.path.length > 12 then b.path.take 5 ++ [`«…»] ++ b.path.drop (b.path.length - 6)
    else b.path
  m!"• `{b.name}`: {b.reason}\n    via {" → ".intercalate (shown.map toString)}"

/-- Where an evaluation that reached neither `true` nor `false` is stuck: the kernel's weak head normal
form of `e` is followed into the major premise of a stuck recursor (or the structure of a stuck
projection, or the quotient of a stuck `Quot.lift`) until its head is none of these. Returns the stuck
term and the last definition unfolded on the way (the one whose body holds the stuck construct).
Diagnostics only, after a failed check: each step re-evaluates its subterm, so the search stops after
`budgetMs`. -/
partial def findStuck (e : Expr) (budgetMs : Nat := 20000) : MetaM (Option (Expr × Option Name)) := do
  let env ← getEnv
  let t0 ← IO.monoMsNow
  let rec go (e : Expr) (via : Option Name) (depth : Nat) : MetaM (Option (Expr × Option Name)) := do
    if depth > 64 || (← IO.monoMsNow) - t0 > budgetMs then return none
    let via := match e.getAppFn with
      | .const c _ => if env.find? c matches some (.defnInfo _) then some c else via
      | _ => via
    let .ok r := Kernel.whnf env {} e | return none
    let args := r.getAppArgs
    match r.getAppFn with
    | .const c _ =>
      match env.find? c with
      | some (.recInfo rv) =>
        -- a K-like recursor (`Eq.rec`) that did not reduce: its endpoints differ, stuck right here
        if rv.k then return some (r, via)
        let i := rv.numParams + rv.numMotives + rv.numMinors + rv.numIndices
        if h : i < args.size then go args[i] via (depth + 1) else return some (r, via)
      | some (.quotInfo _) => if h : 5 < args.size then go args[5] via (depth + 1) else return some (r, via)
      | _ => return some (r, via)
    | .proj _ _ s => go s via (depth + 1)
    | _ => return some (r, via)
  go e none 0

/-- A report on the stuck point found by `findStuck`. -/
def stuckMessage (r : Expr) (via : Option Name) : MetaM MessageData := do
  let env ← getEnv
  let shown ← try pure (toString (← ppExpr r)) catch _ => pure (toString r)
  let shown := if shown.length > 600 then s!"{shown.take 600} …" else shown
  let inDef := match via with | some c => m!" (in the body of `{c}`)" | none => m!""
  let head := r.getAppFn.constName?.getD .anonymous
  let isK := match env.find? head with | some (.recInfo rv) => rv.k | _ => false
  let what := if isK then
      m!"a cast (`{head}`: `h ▸ x`, `Eq.mpr`, `cast`) along an equality whose two sides are not \
        definitionally equal (its proof goes through `propext` or `Quot.sound`, as in instances built \
        with `simp`/`rw`, or a cast along an equality of quotients); the kernel cannot reduce such a \
        cast, compiled code erases it. A version of the definition without the cast can be registered \
        with `@[kernel_replace]`"
    else m!"`{head}`, which the kernel does not reduce further"
  let label := match via with | some c => c | none => head
  return m!"• `{label}`: the kernel evaluation is stuck at {what}{inDef}.\n    stuck term: {shown}"

/-- Explain why the kernel did not prove `e' = true`. -/
def diagnose (e' : Expr) (lvls : List Name) (kernelEx : Exception) (native? : Option Bool)
    (cfg : KernelConfig) : MetaM MessageData := do
  let mut msg := m!"the kernel did not reduce the decision procedure to `true`.\n\
    Kernel message: {kernelEx.toMessageData}"
  let mismatch := (← kernelEx.toMessageData.toString).contains "type mismatch"
  let mut kernelFalse := false
  if cfg.diagnoseFalse && mismatch then
    let probe ← mkAuxDeclName `_kt_false
    if let .ok _ ← tryAddTheorem probe lvls (mkBoolEq e' boolFalse) (reflBool boolFalse) cfg then
      kernelFalse := true
  if kernelFalse then
    msg := msg ++ m!"\n\nThe kernel evaluates the decision procedure to `false`: the \
      proposition is FALSE according to the logical definitions."
    if native? == some true then
      msg := msg ++ m!" Compiled code evaluated it to `true`, so compiled code and logic \
        disagree. Typical causes: an `@[implemented_by]`/`@[extern]` implementation that differs \
        from its definition, or platform-dependent behaviour."
      let srcs ← findCompiledSources e'
      unless srcs.isEmpty do
        msg := msg ++ m!"\nReachable constants whose compiled code is not their definition:\n" ++
          MessageData.joinSep (srcs.toList.map fun (c, s) => s.toMessageData c) "\n"
    return msg
  let blockers ← findBlockers e' (skipProofs := cfg.transport)
  -- the kernel finished but reached neither `true` nor `false`: find where it is stuck
  let stuck ← if blockers.isEmpty && mismatch then
      try findStuck e' catch _ => pure none
    else pure none
  if let some (r, via) := stuck then
    msg := msg ++ m!"\n\nNo constant without a kernel definition is reachable, but the evaluation \
      reached neither `true` nor `false`:\n" ++ (← stuckMessage r via)
  else if blockers.isEmpty then
    msg := msg ++ m!"\n\nNo constant without a kernel definition is reachable, so the kernel \
      ran out of resources (time, recursion depth or memory) or met a construct it reduces \
      too slowly. Try `kdecide (config := \{ maxHeartbeats := 0, maxRecDepth := … })`, or split \
      the proposition."
  else
    msg := msg ++ m!"\n\nReachable constants that the kernel cannot unfold (evaluation gets stuck \
      if it reaches one of them):\n" ++
      MessageData.joinSep (blockers.toList.map Blocker.toMessageData) "\n"
  return msg

/-! ## Main entry point -/

structure KernelResult where
  /-- The theorem `e = true`. -/
  thm : Name
  /-- Kernel-reducible copies created. -/
  copies : Array Name
  /-- Time of the kernel evaluation in ms. -/
  ms : Nat
  /-- Proved through the accessibility-generator route (`accFallback`; Lean ≤ 4.36 only). -/
  viaAcc : Bool := false

/-- Add `name : e = true`, proved by kernel evaluation of `e` (a closed `Bool` term), and check
that the result depends on no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
`native?` is the result of compiled evaluation, if known (used in diagnostics only). -/
def proveTrueByKernelCore (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  -- reachable blockers: bounded evaluation (see `KernelConfig.blockedHeartbeats`)
  let t0 ← IO.monoMsNow
  let bounded ← if cfg.blockedHeartbeats != 0 &&
      (cfg.maxHeartbeats == 0 || cfg.maxHeartbeats > cfg.blockedHeartbeats) then do
      pure !(← findBlockers e (static := cfg.wf)).isEmpty
    else pure false
  -- registered replacements always apply; `cfg.wf` only controls the `WellFounded.fix` transform
  let t1 ← IO.monoMsNow
  let ccfg : CopyConfig := { opt := cfg.opt, wf := cfg.wf, wfAcc := cfg.wfAcc, trace := cfg.trace, skipUnchanged := cfg.skipUnchanged, transport := cfg.transport }
  let r ← kernelCopy e ccfg
  let t2 ← IO.monoMsNow
  if cfg.trace then
    eprintRaw s!"NT {name} blockers_ms={t1 - t0} bounded={bounded} copy_ms={t2 - t1} \
      copies={r.created.size} copy_kernel_ms={r.timings.foldl (fun a (_, x, y, _) => a + x + y) 0}"
  let e' := r.expr
  let target := mkBoolEq e boolTrue
  let cfg := if bounded then { cfg with maxHeartbeats := cfg.blockedHeartbeats } else cfg
  let fail (ex : Exception) : MetaM KernelResult := do
    let mut msg ← diagnose e' lvls ex native? cfg
    if bounded then
      msg := msg ++ m!"\n\nThe evaluation was bounded to {cfg.blockedHeartbeats} thousand \
        heartbeats because such constants are reachable; \
        `(config := \{ blockedHeartbeats := 0 })` removes the bound."
    throwError msg
  -- a failed attempt leaves only its copies behind, as a failed evaluation always did
  -- (`tryAddTheorem` restores the environment): the evaluation theorem `name.eval`, which stays
  -- when the bridge is rejected after it, and `name`, when its axioms are rejected, are removed
  -- again. Left behind, they made the retries in `proveTrueByKernel` fail at once ("constant has
  -- already been declared"), whatever the retry's copies
  let envEval ← getEnv
  try
    let ms ← if e' == e then
      match ← tryAddTheorem name lvls target (reflBool boolTrue) cfg with
      | .ok ms => pure ms
      | .error ex => return ← fail ex
    else do
      let evalName := name ++ `eval
      let ms ← match ← tryAddTheorem evalName lvls (mkBoolEq e' boolTrue) (reflBool boolTrue) cfg with
        | .ok ms => pure ms
        | .error ex => return ← fail ex
      let evalThm := mkConst evalName (lvls.map mkLevelParam)
      let viaEq (h : Expr) := mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) e e' boolTrue h evalThm
      -- preferred: congruence from the per-constant equations; fallback: `rfl`
      let mut done := false
      let eqs : NameMap (Name × Name) := r.replaced.foldl (fun m (c, c', h) => m.insert c (c', h)) {}
      if let some h ← congrSubst e (mkConst ``Bool) eqs then
        if let .ok _ ← tryAddTheorem name lvls target (viaEq h) cfg then done := true
      unless done do
        if let .error ex ← tryAddTheorem name lvls target (viaEq (reflBool e)) cfg then
          throwError m!"NativeTrust internal error: the kernel rejected the bridge from the \
            original term to its kernel-reducible copy:\n{ex.toMessageData}"
      pure ms
    if cfg.trace then eprintRaw s!"NT {name} eval_ms={ms}"
    let axs ← collectAxioms name
    let bad := axs.filter (!stdAxioms.contains ·)
    unless bad.isEmpty do
      throwError m!"NativeTrust: the kernel proof uses non-standard axioms {bad.toList}"
    return { thm := name, copies := r.created, ms, viaAcc := cfg.wfAcc }
  catch ex =>
    setEnv envEval
    throw ex

/-- `proveTrueByKernelCore` with the fuel route, and the accessibility-generator route as a
fallback when well-founded recursion is what stops the fuel route (`KernelConfig.accFallback`). -/
def proveTrueByKernel (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  try proveTrueByKernelCore e name lvls cfg native?
  catch ex =>
    unless cfg.wf && !cfg.wfAcc do throw ex
    -- only when well-founded recursion is reachable at all
    unless (← findBlockers e).any (·.name == ``WellFounded.fix) do throw ex
    -- the fuel route once more, with the proofs inside rejected copies transported along the copy
    -- equations and unchanged copies skipped (own copy names): a retry, so that every fact the
    -- first attempt converts is converted exactly as before
    if !cfg.transport then
      if cfg.trace then eprintRaw s!"NT {name} fuel-retry-transport"
      try
        return (← proveTrueByKernelCore e name lvls { cfg with transport := true, skipUnchanged := true } native?)
      catch exRetry =>
        -- the report below shows the first attempt's error; the retry's goes to the trace
        if cfg.trace then
          let m := (← exRetry.toMessageData.toString).replace "\n" " "
          eprintRaw s!"NT {name} fuel-retry-failed {m.take 400}"
    unless cfg.accFallback do throw ex
    if cfg.trace then eprintRaw s!"NT {name} acc-fallback"
    try proveTrueByKernelCore e name lvls { cfg with wfAcc := true } native?
    catch ex' =>
      -- report both: the retry can fail for another reason than the fuel route
      throwError m!"{ex.toMessageData}\n\nRetried with the accessibility-generator route \
        (`wfAcc`), which failed too:\n{ex'.toMessageData}"

/-! ## Splitting -/

/-- `l` as an explicit list `[x₁, …, xₙ]` (a chain of `List.cons` ending in `List.nil`), with
its element type and universe level. -/
partial def listLiteral? (l : Expr) : Option (Expr × Level × Array Expr) :=
  go l #[]
where
  go (l : Expr) (acc : Array Expr) : Option (Expr × Level × Array Expr) :=
    match l.getAppFn, l.getAppArgs with
    | .const ``List.cons [_], #[_, x, t] => go t (acc.push x)
    | .const ``List.nil [u], #[α] => some (α, u, acc)
    | _, _ => none

def mkListLit (α : Expr) (u : Level) (xs : Array Expr) : Expr :=
  xs.foldr (fun x t => mkApp3 (mkConst ``List.cons [u]) α x t) (mkApp (mkConst ``List.nil [u]) α)

/-- Unfold the head of the closed `Bool` term `e` (definitions, `decide` of a `b = true`
proposition, projections of instances) until it is `a && b` or `List.all l f` with `l` an
explicit list of at least two elements. -/
partial def findSplit (e : Expr) (fuel : Nat := 64) : MetaM (Option Expr) :=
  withTransparency .all do
    let rec loop (e : Expr) : Nat → MetaM (Option Expr)
      | 0 => pure none
      | n + 1 => do
        let e ← whnfCore e
        match e.getAppFn, e.getAppArgs with
        | .const ``and _, #[_, _] => return some e
        | .const ``List.all _, #[_, l, _] =>
          -- an explicit list, or a computed one (split by index; no evaluation here)
          match listLiteral? (← instantiateMVars l) with
          | some (_, _, xs) => return if xs.size ≥ 2 then some e else none
          | none => return some e
        | _, _ =>
          match ← unfoldDefinition? e with
          | some e' => loop e' n
          | none => return none
    loop e fuel

/-- Prove `e = true` for a closed `Bool` term by kernel evaluation, split into up to
`cfg.split` kernel declarations named `name.p<i>` (see `KernelConfig.split`). Returns the name
of the theorem `name : e = true`. -/
partial def proveTrueSplit (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  let counter ← IO.mkRef 0
  let total ← IO.mkRef 0
  let copies ← IO.mkRef (#[] : Array Name)
  let viaAcc ← IO.mkRef false
  -- `l.all f = true` for a computed list `l`: chunks `(R.take k)` of `R = l.drop …`, joined by
  -- `all_take_drop_true`. Compiled code proposes the length (a hint only); the last chunk is the
  -- remaining suffix, so a wrong hint costs time, not soundness.
  let splitByIndex (u : Level) (α l f : Expr) (budget : Nat) (leaf : MetaM Expr) :
      MetaM Expr := do
    let n ← match ← nativeEvalNat (mkApp2 (mkConst ``List.length [u]) α l) with
      | .ok n => pure n
      | .error _ => return ← leaf
    let k := min budget n
    if k ≤ 1 then return ← leaf
    let take (m : Nat) (r : Expr) := mkApp3 (mkConst ``List.take [u]) α (mkNatLit m) r
    let drop (m : Nat) (r : Expr) := mkApp3 (mkConst ``List.drop [u]) α (mkNatLit m) r
    let allOf (r : Expr) := mkApp3 (mkConst ``List.all [u]) α r f
    -- suffixes R₀ = l, R_{j+1} = R_j.drop c_j, with chunk sizes c_j
    let sizes := (List.range k).toArray.map fun j => (j + 1) * n / k - j * n / k
    let mut suffixes := #[l]
    for j in [0:k - 1] do
      suffixes := suffixes.push (drop sizes[j]! suffixes[j]!)
    let mut pieces := #[]
    for j in [0:k] do
      let chunk := if j + 1 < k then take sizes[j]! suffixes[j]! else suffixes[j]!
      let i ← counter.modifyGet fun i => (i, i + 1)
      let r ← proveTrueByKernel (allOf chunk) (name ++ (`p).appendIndexAfter i) lvls cfg native?
      total.modify (· + r.ms)
      copies.modify (· ++ r.copies)
      if r.viaAcc then viaAcc.set true
      pieces := pieces.push (mkConst r.thm (lvls.map mkLevelParam))
    let mut acc := pieces.back!
    for j in (List.range (k - 1)).reverse do
      acc := mkApp6 (mkConst ``NativeTrust.all_take_drop_true [u]) α f suffixes[j]!
        (mkNatLit sizes[j]!) pieces[j]! acc
    return acc
  -- returns a proof of `e = true`
  let rec go (e : Expr) (budget : Nat) : MetaM Expr := do
    let leaf : MetaM Expr := do
      let i ← counter.modifyGet fun i => (i, i + 1)
      let r ← proveTrueByKernel e (name ++ (`p).appendIndexAfter i) lvls cfg native?
      total.modify (· + r.ms)
      copies.modify (· ++ r.copies)
      if r.viaAcc then viaAcc.set true
      return mkConst r.thm (lvls.map mkLevelParam)
    if budget ≤ 1 then return ← leaf
    -- `decide (b = true)` is `b`
    if e.isAppOfArity ``Decidable.decide 2 then
      if let some (_, b, rhs) := (e.getArg! 0).eq? then
        if rhs.isConstOf ``Bool.true then
          let hb ← go b budget
          return mkApp3 (mkConst ``NativeTrust.decide_eq_true_of) b (e.getArg! 1) hb
    -- splitting is an optimisation: if looking for a split fails, check `e` as a whole
    let split? ← try findSplit e catch _ => pure none
    match split? with
    | some s =>
      match s.getAppFn, s.getAppArgs with
      | .const ``and _, #[a, b] =>
        let ha ← go a (budget / 2)
        let hb ← go b (budget - budget / 2)
        -- `(a && b) = true`; the kernel checks that `e` unfolds to `a && b`
        return mkApp4 (mkConst ``NativeTrust.and_true_of) a b ha hb
      | .const ``List.all [u], #[α, l, f] =>
        let some (_, _, xs) := listLiteral? l | splitByIndex u α l f budget leaf
        let k := min budget xs.size
        -- chunks of (almost) equal size
        let chunks := (List.range k).toArray.map fun j =>
          xs.extract (j * xs.size / k) ((j + 1) * xs.size / k)
        let proofs ← chunks.mapM fun c => go (mkApp3 (mkConst ``List.all [u]) α (mkListLit α u c) f) 1
        -- combine right to left: (c₁ ++ (c₂ ++ …)).all f = true
        let mut acc := proofs.back!
        let mut accList := mkListLit α u chunks.back!
        for j in (List.range (k - 1)).reverse do
          let cj := mkListLit α u chunks[j]!
          acc := mkApp6 (mkConst ``NativeTrust.all_append_true [u]) α f cj accList proofs[j]! acc
          accList := mkApp4 (mkConst ``HAppend.hAppend [u, u, u]) (mkApp (mkConst ``List [u]) α)
            (mkApp (mkConst ``List [u]) α) (mkApp (mkConst ``List [u]) α)
            (mkApp2 (mkConst ``instHAppendOfAppend [u]) (mkApp (mkConst ``List [u]) α)
              (mkApp (mkConst ``List.instAppend [u]) α)) |> (mkApp2 · cj accList)
        return acc
      | _, _ => leaf
    | none => leaf
  if cfg.split ≤ 1 then return ← proveTrueByKernel e name lvls cfg native?
  let pf ← go e cfg.split
  match ← tryAddTheorem name lvls (mkBoolEq e boolTrue) pf cfg with
  | .ok _ => pure ()
  | .error ex => throwError m!"NativeTrust: the kernel rejected the assembly of the split \
      check:\n{ex.toMessageData}"
  let axs ← collectAxioms name
  let bad := axs.filter (!stdAxioms.contains ·)
  unless bad.isEmpty do
    throwError m!"NativeTrust: the kernel proof uses non-standard axioms {bad.toList}"
  return { thm := name, copies := ← copies.get, ms := ← total.get, viaAcc := ← viaAcc.get }

end NativeTrust
