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
  /-- Passed to the copier (`CopyConfig.fastLitMin`): string literals of at least this many
  characters are evaluated through `ofListFast` (linear) instead of `String.ofList` (quadratic);
  `0` = off. -/
  fastLitMin : Nat := 128
  /-- Heartbeat budget (in thousands) for each Meta-level search for structure (where to split, the
  shape of the proposition, instances for its parts). The search only proposes a decomposition, and
  the kernel checks every piece and the assembly, so giving up is always safe: the term is then
  checked as a whole. Without a budget, the search can evaluate the decision procedure in Meta-level
  `whnf` (unfolding `decide` reduces the instance), which is far slower than the kernel and was seen
  to exhaust 48 GB before the kernel started. `0` = no budget. -/
  searchHeartbeats : Nat := 5000
  /-- Before any structure search (`split`, `witness`, `propSplit`), try the whole term once in the
  kernel with this heartbeat limit (thousands; about 2 s per 1000): a cheap term is then proved as it
  stands, and only expensive terms pay for the search. The search can cost far more than the kernel:
  a heartbeat budget does not bound one large allocation, and a minidregg fact that the kernel proves
  in 0.08 s exhausted 21 GB in the search. `0` = no first attempt; not used with `shards`. -/
  quickHeartbeats : Nat := 2000
  /-- Witnesses: a `List.any`, an existential `∃ x < n, P x` or `∃ x ∈ l, P x` is checked at one
  witness that compiled code proposes (the first index where the predicate holds), so the kernel
  evaluates the predicate once instead of on every earlier candidate. Compiled code is an untrusted
  oracle here as everywhere: only the kernel-checked instance enters the proof. -/
  witness : Bool := true
  /-- Structured checks of propositions (`decide p = true`) along their logical structure:
  conjunctions are split like `&&`; `∀ x < n, P x`, `¬ ∃ x < n, P x` and `∀ x ∈ l, P x` are checked as
  `List.all` (split by index, so `split`/`shards` apply); a disjunction or a negated conjunction is
  checked at the one disjunct or false conjunct that compiled code names. The parts are decided with
  instances found by synthesis, which can differ from the instance inside the original decision
  procedure. On 26 zcash facts run both ways it converted 7 more than the plain check and lost none,
  but it has not been run over the facts that convert today, so it is off by default: meant for a
  pass over facts that fail for resources, and implied by `shards`. -/
  propSplit : Bool := false
  /-- Multi-module sharding: split into up to this many kernel declarations (like `split`) with
  module-independent names `_ktshard.<fact>.s<i>`, so each piece can be proved in its own process
  (`shardOnly`) and the pieces combined in a module that imports them. `0` = off. -/
  shards : Nat := 0
  /-- With `shards`: prove only piece `shardOnly - 1` (nothing is assembled); `0` = combine the pieces,
  which must be imported. -/
  shardOnly : Nat := 0
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
  /-- Kernel declarations (pieces) of a structured check. -/
  pieces : Nat := 1

/-- Add `name : e = true`, proved by kernel evaluation of `e` (a closed `Bool` term), and check
that the result depends on no axioms beyond `propext`, `Classical.choice` and `Quot.sound`.
`native?` is the result of compiled evaluation, if known (used in diagnostics only). -/
def proveTrueByKernelCore (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  -- functions applied to long string literals (`@[kernel_string_arg]`): `sPf? : e = e₀`
  let (e₀, sPf?) ← match ← strArgSubst e (mkConst ``Bool) cfg.fastLitMin with
    | some (h, v) => pure (v, some h)
    | none => pure (e, none)
  -- reachable blockers: bounded evaluation (see `KernelConfig.blockedHeartbeats`)
  let t0 ← IO.monoMsNow
  let bounded ← if cfg.blockedHeartbeats != 0 &&
      (cfg.maxHeartbeats == 0 || cfg.maxHeartbeats > cfg.blockedHeartbeats) then do
      pure !(← findBlockers e₀ (static := cfg.wf)).isEmpty
    else pure false
  -- registered replacements always apply; `cfg.wf` only controls the `WellFounded.fix` transform
  let t1 ← IO.monoMsNow
  let ccfg : CopyConfig := { opt := cfg.opt, wf := cfg.wf, wfAcc := cfg.wfAcc, trace := cfg.trace, skipUnchanged := cfg.skipUnchanged, transport := cfg.transport, fastLitMin := cfg.fastLitMin }
  let r ← kernelCopy e₀ ccfg
  -- long string literals in the decided term itself: `litPf? : e₁ = e'`
  let e₁ := r.expr
  let forms := longLitForms cfg.fastLitMin e₁
  let (e', litPf?) ← if forms.isEmpty then pure (e₁, none) else
    match ← litSubst e₁ (mkConst ``Bool) forms with
    | some (h, v) => pure (v, some h)
    | none => pure (e₁, none)
  let t2 ← IO.monoMsNow
  if cfg.trace then
    eprintRaw s!"NT {name} blockers_ms={t1 - t0} bounded={bounded} copy_ms={t2 - t1} \
      copies={r.created.size} copy_kernel_ms={r.timings.foldl (fun a (_, x, y, _) => a + x + y) 0} \
      fast_lits={forms.size} string_args={sPf?.isSome}"
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
      -- `e = e₀` (string arguments), `h : e₀ = e₁` (constants), `e₁ = e'` (literals)
      let bridge (h : Expr) : Expr :=
        let h := match litPf? with
          | some hl => mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) e₀ e₁ e' h hl
          | none => h
        match sPf? with
        | some hs => mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) e e₀ e' hs h
        | none => h
      let viaEq (h : Expr) := mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) e e' boolTrue (bridge h) evalThm
      -- preferred: congruence from the per-constant equations; fallback: `rfl`
      let mut done := false
      let eqs : NameMap (Name × Name) := r.replaced.foldl (fun m (c, c', h) => m.insert c (c', h)) {}
      if let some h ← congrSubst e₀ (mkConst ``Bool) eqs then
        if let .ok _ ← tryAddTheorem name lvls target (viaEq h) cfg then done := true
      else if e₁ == e₀ && (litPf?.isSome || sPf?.isSome) then
        -- no constant was replaced
        if let .ok _ ← tryAddTheorem name lvls target (viaEq (reflBool e₀)) cfg then done := true
      unless done do
        if let .error ex ← tryAddTheorem name lvls target (viaEq (reflBool e₀)) cfg then
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

/-- Run a Meta-level structure search under a heartbeat budget (thousands; `0` = none). `none` when
the budget runs out or the search throws, runtime exceptions (deep recursion, heartbeats) included:
a search only proposes a decomposition, so giving up is safe. -/
def boundedSearch {α : Type} (budget : Nat) (x : MetaM (Option α)) : MetaM (Option α) := do
  let x := if budget == 0 then x else do
    let hb ← IO.getNumHeartbeats
    withTheReader Core.Context (fun c => { c with initHeartbeats := hb, maxHeartbeats := budget * 1000 }) x
  tryCatchRuntimeEx x (fun _ => pure none)

/-- Evaluate a closed `Nat` term with compiled code, if it compiles; untrusted (a hint). -/
def nativeNat? (e : Expr) : MetaM (Option Nat) := do
  match ← (try nativeEvalNat e catch _ => pure (.error m!"")) with
  | .ok n => pure (some n)
  | .error _ => pure none

/-- Evaluate a closed `Bool` term with compiled code, if it compiles; untrusted (a hint). -/
def nativeBool? (e : Expr) : MetaM (Option Bool) := do
  match ← (try nativeEval e catch _ => pure (.error m!"")) with
  | .ok b => pure (some b)
  | .error _ => pure none

/-- A `Decidable` instance for `p` found by instance synthesis (bounded), if any. -/
def synthDecidable? (p : Expr) (budget : Nat) : MetaM (Option Expr) :=
  boundedSearch budget do
    let i ← synthInstance (mkApp (mkConst ``Decidable) p)
    let i ← instantiateMVars i
    if i.hasMVar then return none else return some i

/-- `fun x => inst` for `∀ x : α, Decidable (body x)` (`body` has the loose bound variable 0). -/
def synthDecidablePred? (α : Expr) (body : Expr) (budget : Nat) : MetaM (Option Expr) :=
  boundedSearch budget do
    withLocalDeclD `x α fun x => do
      let i ← synthInstance (mkApp (mkConst ``Decidable) (body.instantiate1 x))
      let i ← instantiateMVars i
      if i.hasMVar then return none else return some (← mkLambdaFVars #[x] i)

/-- Shapes of propositions that `proveTrueSplit` checks structurally. -/
inductive PropShape where
  | and (a b : Expr)
  | or (a b : Expr)
  | notAnd (a b : Expr)
  /-- `∀ x, x < n → P x`: `P` as a lambda. -/
  | forallLt (n P : Expr)
  /-- `∀ x, x ∈ l → P x` over `l : List α`. -/
  | forallMem (u : Level) (α l P : Expr)
  /-- `¬ ∃ x, x < n ∧ P x`. -/
  | notExistsLt (n P : Expr)
  /-- `∃ x, x < n ∧ P x`: `body` is the lambda `fun x => x < n ∧ P x`. -/
  | existsLt (n body : Expr)
  /-- `∃ x, x ∈ l ∧ P x`. -/
  | existsMem (u : Level) (α l P : Expr)

/-- `x < n` for the loose bound variable `x = #0`, with `n` closed: `n`. -/
def ltBound? (t : Expr) : Option Expr :=
  if t.isAppOfArity ``LT.lt 4 && (t.getArg! 0).isConstOf ``Nat && (t.getArg! 2) == .bvar 0 &&
      !(t.getArg! 3).hasLooseBVars then some (t.getArg! 3)
  else none

/-- `x ∈ l` for the loose bound variable `x = #0`, with `l : List α` closed: `(u, α, l)`. -/
def memList? (t : Expr) : Option (Level × Expr × Expr) :=
  -- `Membership.mem` (argument order changed in 2024: collection first)
  if t.isAppOfArity ``Membership.mem 5 then
    let a3 := t.getArg! 3; let a4 := t.getArg! 4
    let (coll, x) := if a4 == .bvar 0 then (a3, a4) else (a4, a3)
    if x != .bvar 0 || coll.hasLooseBVars then none else
    match (t.getArg! 1).getAppFn, (t.getArg! 1).getAppArgs with
    | .const ``List [u], #[α] => some (u, α, coll)
    | _, _ => none
  else none

/-- Unfold `p` (reducible steps, then definitions) until `stop` holds (at most `fuel` unfoldings). -/
partial def unfoldPropUntil (p : Expr) (fuel : Nat) (stop : Expr → Bool) : MetaM (Option Expr) := do
  let mut p := p
  for _ in [0:fuel] do
    p ← whnfR (← instantiateMVars p)
    if stop p then return some p
    match ← unfoldDefinition? p with
    | some p' => p := p'
    | none => return none
  return none

def mkNotE (p : Expr) : Expr := mkApp (mkConst ``Not) p

/-- Unfold the proposition `p` until it has one of the shapes of `PropShape`. The result is
definitionally equal to `p` by unfolding (the kernel checks it cheaply; no evaluation is needed). -/
def findPropShape (p : Expr) : MetaM (Option (Expr × PropShape)) := do
  let isHead (p : Expr) : Bool := p.isAppOfArity ``And 2 || p.isAppOfArity ``Or 2 ||
    p.isAppOfArity ``Not 1 || p.isAppOfArity ``Exists 2 || p.isForall
  let some p ← unfoldPropUntil p 32 isHead | return none
  if p.isAppOfArity ``And 2 then return some (p, .and (p.getArg! 0) (p.getArg! 1))
  if p.isAppOfArity ``Or 2 then return some (p, .or (p.getArg! 0) (p.getArg! 1))
  if p.isAppOfArity ``Not 1 then
    let some q ← unfoldPropUntil (p.getArg! 0) 32 (fun q => q.isAppOfArity ``And 2 || q.isAppOfArity ``Exists 2)
      | return none
    if q.isAppOfArity ``And 2 then return some (p, .notAnd (q.getArg! 0) (q.getArg! 1))
    if let .lam _ ty b _ := q.getArg! 1 then
      if ty.isConstOf ``Nat && b.isAppOfArity ``And 2 then
        if let some bound := ltBound? (b.getArg! 0) then
          return some (p, .notExistsLt bound (.lam `x ty (b.getArg! 1) .default))
    return none
  if p.isAppOfArity ``Exists 2 then
    if let .lam _ ty b _ := p.getArg! 1 then
      if b.isAppOfArity ``And 2 then
        if ty.isConstOf ``Nat then
          if let some bound := ltBound? (b.getArg! 0) then
            return some (p, .existsLt bound (p.getArg! 1))
        if let some (u, α, l) := memList? (b.getArg! 0) then
          return some (p, .existsMem u α l (.lam `x ty (b.getArg! 1) .default))
    return none
  if let .forallE _ ty b _ := p then
    if let .forallE _ hty body _ := b then
      -- `∀ x, guard x → P x`, with `P` not using the guard's proof
      if !body.hasLooseBVar 0 then
        let body := body.lowerLooseBVars 1 1
        if ty.isConstOf ``Nat then
          if let some bound := ltBound? hty then
            return some (p, .forallLt bound (.lam `x ty body .default))
        if let some (u, α, l) := memList? hty then
          return some (p, .forallMem u α l (.lam `x ty body .default))
  return none

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
proposition, projections of instances) until it is `a && b`, `List.all l f` with `l` an
explicit list of at least two elements or a computed list, or (with `any`) `List.any l f`. -/
partial def findSplit (e : Expr) (fuel : Nat := 64) (any : Bool := false) : MetaM (Option Expr) :=
  withTransparency .all do
    let rec loop (e : Expr) : Nat → MetaM (Option Expr)
      | 0 => pure none
      | n + 1 => do
        let e ← whnfCore e
        if e.isAppOfArity ``and 2 then return some e
        if e.isAppOfArity ``List.all 3 then
          -- an explicit list, or a computed one (split by index; no evaluation here)
          match listLiteral? (← instantiateMVars (e.getArg! 1)) with
          | some (_, _, xs) => return if xs.size ≥ 2 then some e else none
          | none => return some e
        if any && e.isAppOfArity ``List.any 3 then return some e
        match ← unfoldDefinition? e with
        | some e' => loop e' n
        | none => return none
    loop e fuel

/-- State of a structured check (`proveTrueSplit`): one kernel declaration per piece. -/
structure SplitCtx where
  name : Name
  lvls : List Name
  cfg : KernelConfig
  native? : Option Bool
  counter : IO.Ref Nat
  total : IO.Ref Nat
  copies : IO.Ref (Array Name)
  viaAcc : IO.Ref Bool

def SplitCtx.note (c : SplitCtx) (msg : String) : MetaM Unit := do
  if c.cfg.trace then eprintRaw s!"NT {c.name} structure {msg}"

/-- One piece: `e = true` by kernel evaluation, in its own declaration. With `shards`, pieces have
module-independent names `name.s<i>`: a process with `shardOnly := i + 1` proves piece `i` only, and
a process with `shardOnly := 0` uses the pieces it imports (checking each states the piece it
computed itself). -/
def SplitCtx.leaf (c : SplitCtx) (e : Expr) : MetaM Expr := do
  let i ← c.counter.modifyGet fun i => (i, i + 1)
  let us := c.lvls.map mkLevelParam
  let record (r : KernelResult) : MetaM Unit := do
    c.total.modify (· + r.ms); c.copies.modify (· ++ r.copies)
    if r.viaAcc then c.viaAcc.set true
  if c.cfg.shards > 0 then
    let leafName := c.name ++ (`s).appendIndexAfter i
    if c.cfg.shardOnly == 0 then
      let some info := (← getEnv).find? leafName
        | throwError m!"NativeTrust: piece {i} of the sharded check (`{leafName}`) is missing: prove it \
            in its own module with `(config := \{ shards := {c.cfg.shards}, shardOnly := {i + 1} })` and \
            import that module"
      unless info.type == mkBoolEq e boolTrue do
        throwError m!"NativeTrust: the imported piece `{leafName}` states another piece than this \
          process computed:{indentExpr info.type}"
      return mkConst leafName us
    else if i + 1 == c.cfg.shardOnly then
      let r ← proveTrueByKernel e leafName c.lvls c.cfg c.native?
      record r
      return mkConst r.thm us
    else
      -- another process proves this piece; nothing is assembled in this one
      return mkConst leafName us
  let r ← proveTrueByKernel e (c.name ++ (`p).appendIndexAfter i) c.lvls c.cfg c.native?
  record r
  return mkConst r.thm us

/-- `l.all f = true` for a computed list `l`: chunks `(R.take k)` of `R = l.drop …`, joined by
`all_take_drop_true`. Compiled code proposes the length (a hint only); the last chunk is the
remaining suffix, so a wrong hint costs time, not soundness. -/
def SplitCtx.splitByIndex (c : SplitCtx) (u : Level) (α l f : Expr) (budget : Nat) (whole : Expr) :
    MetaM Expr := do
  let some n ← nativeNat? (mkApp2 (mkConst ``List.length [u]) α l) | c.leaf whole
  let k := min budget n
  if k ≤ 1 then return ← c.leaf whole
  c.note s!"all-by-index length={n} pieces={k}"
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
    pieces := pieces.push (← c.leaf (allOf chunk))
  let mut acc := pieces.back!
  for j in (List.range (k - 1)).reverse do
    acc := mkApp6 (mkConst ``NativeTrust.all_take_drop_true [u]) α f suffixes[j]!
      (mkNatLit sizes[j]!) pieces[j]! acc
  return acc

/-- `fun x => @decide (P x) (inst x)` (beta-redexes kept, as in the statements of the lemmas). -/
def decidePred (α P inst : Expr) : Expr :=
  .lam `x α (mkApp2 (mkConst ``Decidable.decide) (mkApp P (.bvar 0)) (mkApp inst (.bvar 0))) .default

mutual

/-- A proof of `e = true` for a closed `Bool` term, split into up to `budget` pieces. -/
partial def goBool (c : SplitCtx) (e : Expr) (budget : Nat) : MetaM Expr := do
  let cfg := c.cfg
  if e.isAppOfArity ``Decidable.decide 2 then
    let p := e.getArg! 0
    -- `decide (b = true)` is `b`
    if let some (_, b, rhs) := p.eq? then
      if rhs.isConstOf ``Bool.true && budget > 1 then
        let hb ← goBool c b budget
        return mkApp3 (mkConst ``NativeTrust.decide_eq_true_of) b (e.getArg! 1) hb
    -- a proposition with structure: prove `p`, then `decide p = true` for the instance in `e`
    if cfg.witness || cfg.propSplit || cfg.shards > 0 then
      let n0 ← c.counter.get
      let r ← tryCatchRuntimeEx (goProp c p budget) fun ex => do
        if cfg.shards > 0 then throw ex
        let msg ← ex.toMessageData.toString
        -- a piece's kernel evaluation failed: the whole term contains that piece, so it would fail too
        if ["the kernel did not reduce", "deep recursion", "deterministic timeout", "maximum recursion",
            "out of memory"].any (fun pat => (msg.splitOn pat).length > 1) then throw ex
        c.note s!"failed, checking the whole term: {msg.take 200}"
        pure none
      if let some hp := r then
        return mkApp3 (mkConst ``decide_eq_true) p (e.getArg! 1) hp
      if (← c.counter.get) != n0 && cfg.shards > 0 then
        throwError "NativeTrust: structured check abandoned after pieces were made"
  if budget ≤ 1 && !cfg.witness then return ← c.leaf e
  -- splitting is an optimisation: if looking for a split fails, check `e` as a whole
  let split? ← boundedSearch cfg.searchHeartbeats (findSplit e (any := cfg.witness))
  let some s := split? | c.leaf e
  match s.getAppFn, s.getAppArgs with
  | .const ``and _, #[a, b] =>
    if budget ≤ 1 then return ← c.leaf e
    let ha ← goBool c a (budget / 2)
    let hb ← goBool c b (budget - budget / 2)
    -- `(a && b) = true`; the kernel checks that `e` unfolds to `a && b`
    return mkApp4 (mkConst ``NativeTrust.and_true_of) a b ha hb
  | .const ``List.all [u], #[α, l, f] =>
    if budget ≤ 1 then return ← c.leaf e
    let some (_, _, xs) := listLiteral? l | c.splitByIndex u α l f budget e
    let k := min budget xs.size
    -- chunks of (almost) equal size
    let chunks := (List.range k).toArray.map fun j =>
      xs.extract (j * xs.size / k) ((j + 1) * xs.size / k)
    let proofs ← chunks.mapM fun ch => c.leaf (mkApp3 (mkConst ``List.all [u]) α (mkListLit α u ch) f)
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
  | .const ``List.any [u], #[α, l, f] =>
    -- witness: the first index where compiled code finds `f` true; the kernel evaluates `f` there only
    let some i ← nativeNat? (mkApp3 (mkConst ``List.findIdx [u]) α f l) | c.leaf e
    let some len ← nativeNat? (mkApp2 (mkConst ``List.length [u]) α l) | c.leaf e
    if i ≥ len then return ← c.leaf e
    c.note s!"witness any index={i} of {len}"
    let rest := mkApp3 (mkConst ``List.drop [u]) α (mkNatLit i) l
    let h ← c.leaf (mkApp3 (mkConst ``List.any [u]) α rest f)
    return mkApp5 (mkConst ``NativeTrust.any_of_drop_any [u]) α f l (mkNatLit i) h
  | _, _ => c.leaf e

/-- A proof of the proposition `q`: structurally (`goProp`), else `decide q = true` with an instance
found by synthesis. -/
partial def proveProp (c : SplitCtx) (q : Expr) (budget : Nat) : MetaM Expr := do
  if let some h ← goProp c q budget then return h
  let some inst ← synthDecidable? q c.cfg.searchHeartbeats
    | throwError m!"NativeTrust: no Decidable instance found for a part of the proposition:{indentExpr q}"
  let h ← goBool c (mkApp2 (mkConst ``Decidable.decide) q inst) budget
  return mkApp3 (mkConst ``of_decide_eq_true) q inst h

/-- A proof of the proposition `p` from its structure (`PropShape`), or `none` when it has none. -/
partial def goProp (c : SplitCtx) (p : Expr) (budget : Nat) : MetaM (Option Expr) := do
  let hb := c.cfg.searchHeartbeats
  let some (_, shape) ← boundedSearch hb (findPropShape p) | return none
  let natT := mkConst ``Nat
  let ps := c.cfg.propSplit || c.cfg.shards > 0
  let witnessShape := match shape with
    | .existsLt .. | .existsMem .. => true
    | _ => false
  if !ps && !witnessShape then return none
  match shape with
  | .and a b =>
    if budget < 2 then return none
    c.note "and"
    let ha ← proveProp c a (budget / 2)
    let hb' ← proveProp c b (budget - budget / 2)
    return some (mkApp4 (mkConst ``And.intro) a b ha hb')
  | .or a b =>
    let some ia ← synthDecidable? a hb | return none
    let some va ← nativeBool? (mkApp2 (mkConst ``Decidable.decide) a ia) | return none
    c.note s!"witness or {if va then "left" else "right"}"
    if va then return some (mkApp3 (mkConst ``Or.inl) a b (← proveProp c a budget))
    else return some (mkApp3 (mkConst ``Or.inr) a b (← proveProp c b budget))
  | .notAnd a b =>
    let some ia ← synthDecidable? a hb | return none
    let some va ← nativeBool? (mkApp2 (mkConst ``Decidable.decide) a ia) | return none
    c.note s!"witness not-and {if va then "right" else "left"}"
    if !va then return some (mkApp3 (mkConst ``NativeTrust.not_and_of_not_left) a b (← proveProp c (mkNotE a) budget))
    else return some (mkApp3 (mkConst ``NativeTrust.not_and_of_not_right) a b (← proveProp c (mkNotE b) budget))
  | .forallLt n P =>
    if budget < 2 then return none
    let some inst ← synthDecidablePred? natT P.bindingBody! hb | return none
    c.note "forall-lt as List.all over List.range"
    let allE := mkApp3 (mkConst ``List.all [levelZero]) natT (mkApp (mkConst ``List.range) n) (decidePred natT P inst)
    let h ← goBool c allE budget
    return some (mkApp4 (mkConst ``NativeTrust.forall_lt_of_all_range) P n inst h)
  | .forallMem u α l P =>
    if budget < 2 then return none
    let some inst ← synthDecidablePred? α P.bindingBody! hb | return none
    c.note "forall-mem as List.all"
    let allE := mkApp3 (mkConst ``List.all [u]) α l (decidePred α P inst)
    let h ← goBool c allE budget
    return some (mkApp5 (mkConst ``NativeTrust.forall_mem_of_all [u]) α P l inst h)
  | .notExistsLt n P =>
    if budget < 2 then return none
    let some inst ← synthDecidablePred? natT P.bindingBody! hb | return none
    c.note "not-exists-lt as List.all over List.range"
    let f := Expr.lam `x natT (mkApp (mkConst ``not) (mkApp2 (mkConst ``Decidable.decide)
      (mkApp P (.bvar 0)) (mkApp inst (.bvar 0)))) .default
    let h ← goBool c (mkApp3 (mkConst ``List.all [levelZero]) natT (mkApp (mkConst ``List.range) n) f) budget
    return some (mkApp4 (mkConst ``NativeTrust.not_exists_lt_of_all_range) P n inst h)
  | .existsLt n body =>
    -- witness: the least `x < n` with `body x`, found by compiled code; the kernel checks `body w`
    let some inst ← synthDecidablePred? natT body.bindingBody! hb | return none
    let some i ← nativeNat? (mkApp3 (mkConst ``List.findIdx [levelZero]) natT (decidePred natT body inst)
      (mkApp (mkConst ``List.range) n)) | return none
    let some nv ← nativeNat? n | return none
    if i ≥ nv then return none
    c.note s!"witness exists-lt x={i} (bound {nv})"
    let w := mkNatLit i
    let h ← proveProp c (body.beta #[w]) budget
    return some (mkApp4 (mkConst ``Exists.intro [levelOne]) natT body w h)
  | .existsMem u α l P =>
    let some inst ← synthDecidablePred? α P.bindingBody! hb | return none
    c.note "exists-mem as List.any"
    let h ← goBool c (mkApp3 (mkConst ``List.any [u]) α l (decidePred α P inst)) budget
    return some (mkApp5 (mkConst ``NativeTrust.exists_mem_of_any [u]) α P l inst h)

end

/-- Prove `e = true` for a closed `Bool` term by kernel evaluation, split into up to
`max cfg.split cfg.shards` kernel declarations named `name.p<i>` (`name.s<i>` with `shards`; see
`KernelConfig.split`, `witness`, `shards`). Returns the theorem `name : e = true`; with `shardOnly`,
only the one piece (no theorem `name`). -/
partial def proveTrueSplit (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  let budget := max cfg.split cfg.shards
  if budget ≤ 1 && !cfg.witness then return ← proveTrueByKernel e name lvls cfg native?
  -- a quick whole-term attempt first (bounded kernel evaluation, no diagnosis, no retries)
  if cfg.quickHeartbeats != 0 && cfg.shards == 0 &&
      (cfg.maxHeartbeats == 0 || cfg.maxHeartbeats > cfg.quickHeartbeats) then
    let quick := { cfg with maxHeartbeats := cfg.quickHeartbeats, blockedHeartbeats := 0,
                            diagnoseFalse := false, accFallback := false }
    let r? ← tryCatchRuntimeEx (some <$> proveTrueByKernelCore e name lvls quick native?) fun _ => pure none
    if let some r := r? then
      if cfg.trace then eprintRaw s!"NT {name} quick whole-term attempt proved it"
      return r
    if cfg.trace then eprintRaw s!"NT {name} quick whole-term attempt did not finish; structured check"
  -- functions applied to long string literals (`@[kernel_string_arg]`) are rewritten first, so that the
  -- structured check sees their list-based form
  let (e₀, sPf?) ← match ← strArgSubst e (mkConst ``Bool) cfg.fastLitMin with
    | some (h, v) => pure (v, some h)
    | none => pure (e, none)
  let c : SplitCtx := { name, lvls, cfg, native?, counter := ← IO.mkRef 0, total := ← IO.mkRef 0,
                        copies := ← IO.mkRef #[], viaAcc := ← IO.mkRef false }
  let pf₀ ← goBool c e₀ budget
  let pf := match sPf? with
    | some hs => mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) e e₀ boolTrue hs pf₀
    | none => pf₀
  let pieces ← c.counter.get
  if cfg.trace then eprintRaw s!"NT {name} pieces={pieces}"
  if cfg.shards > 0 && cfg.shardOnly > 0 then
    return { thm := .anonymous, copies := ← c.copies.get, ms := ← c.total.get, viaAcc := ← c.viaAcc.get,
             pieces }
  match ← tryAddTheorem name lvls (mkBoolEq e boolTrue) pf cfg with
  | .ok _ => pure ()
  | .error ex => throwError m!"NativeTrust: the kernel rejected the assembly of the split \
      check:\n{ex.toMessageData}"
  let axs ← collectAxioms name
  let bad := axs.filter (!stdAxioms.contains ·)
  unless bad.isEmpty do
    throwError m!"NativeTrust: the kernel proof uses non-standard axioms {bad.toList}"
  return { thm := name, copies := ← c.copies.get, ms := ← c.total.get, viaAcc := ← c.viaAcc.get, pieces }

end NativeTrust
