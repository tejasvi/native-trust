import Lean
import NativeTrust.Copy
import NativeTrust.CastFree
import NativeTrust.Param
import NativeTrust.CSimpCompat
import NativeTrust.Reify

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
  /-- Heartbeat limit (thousands) for the kernel checks of the definitions copied in the fuel route's retry
  (`transport`). A copy whose check runs out counts as rejected, and its proofs are transported (as for a
  copy the kernel rejects). Without it, a copy that the kernel rejects only after comparing original and
  copied definitions at length can take all the memory (lawful codecs whose proof fields mention the
  copied functions). `0` = no limit. -/
  transportHeartbeats : Nat := 20000
  /-- Passed to the copier (`CopyConfig.keepTypes`); set by the fuel route's retry. -/
  keepTypes : Bool := false
  /-- When the fuel route and its retry fail with well-founded recursion reachable, try the parametric
  route (`NativeTrust.Param`: definitions that occur in types are rewritten together with the types)
  before the accessibility-generator fallback. -/
  param : Bool := true
  /-- When every default route fails and a `@[kernel_fold]` pattern or a `@[kernel_replace_retry]`
  replacement (the `String` functions of `NativeTrust.StrLib`) is reachable, retry once with them
  (`retryRepl`). The default routes never see them, so a fact that converts without them converts
  exactly as before. -/
  foldRetry : Bool := true
  /-- Set by that retry: fold `@[kernel_fold]` patterns and use `@[kernel_replace_retry]` replacements. -/
  retryRepl : Bool := false
  /-- Time budget (ms) of the retry's copying (a retry can have to copy much of what reaches a
  `String` function); the evaluation itself keeps `maxHeartbeats`/`blockedHeartbeats`. -/
  retryMs : Nat := 120000
  /-- Heartbeat limit (thousands) for the kernel checks of the definitions copied in the retry. -/
  retryHeartbeats : Nat := 20000
  /-- Set by the retry: the end of its time budget (`IO.monoMsNow`), `0` = none. -/
  retryDeadline : Nat := 0
  /-- In the retry with retry-only replacements: when its first attempt fails, also run the parametric
  route with them as roots. -/
  paramRetryRepl : Bool := true
  /-- A retry for terms that reach `System.Platform.getNumBits` (`USize`, hence `HashMap`/`HashSet`): the
  platform case split (`proveTrueByKernelPlatform`). -/
  platformCases : Bool := true
  /-- In the platform case split: heartbeat budget (thousands) for checking each case with the hypothesis
  `numBits = v` replaced by a closed stand-in, in a throwaway environment (`probeTheorem`). This shows
  whether the case reduces to `true` (or to `false`) at all, and how much work it takes when the kernel can
  compute `Nat` arithmetic on literals, which it does only in terms without free variables. When the check of
  the first case runs out of this budget, the second case is not checked this way. `0` = no such check. -/
  platformProbeHeartbeats : Nat := 1000
  /-- In the platform case split: when that check succeeds, the evaluation with the hypothesis free may
  take this many times its heartbeats (counted as `IO.getNumHeartbeats` counts them, several per kernel
  heartbeat), and at least `blockedHeartbeats`; beyond that the case fails instead of running on. -/
  platformSlowdown : Nat := 20
  /-- In the platform case split: heartbeat limit (thousands) for each kernel evaluation of a case, whatever the
  check with the stand-in showed, so that the case split always ends (`kdecide`, `kernelize`). The default is
  well above what the largest cases among the study's facts need (the ninegates candidates); `0` = no limit. -/
  platformHeartbeats : Nat := 1000000
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
  /-- When an evaluation is stuck at a cast (`findStuck`) inside a definition whose values are
  `Decidable p` or `Fintype α`, or inside such a definition in its body: build a cast-free version
  of it (`castFreeVersion?`, rules 1-4), prove it equal by `funext` and `Subsingleton.elim`, and retry
  the evaluation once with it, like a registered `@[kernel_replace]`. Applies to the first attempt and
  to the fuel route's retry, not to the accessibility-generator fallback. -/
  castRetry : Bool := true
  /-- How many times the cast retry may run for one attempt: each further round adds cast-free
  versions for the cast at which the previous retry got stuck. -/
  castRounds : Nat := 1
  /-- Staged evaluation (shared intermediate lemmas): when the whole term does not check within
  `quickHeartbeats`, the expensive closed parts of the computation (data constants whose bodies compute
  something, and closed subterms of the decided term) are evaluated by compiled code, the values turned
  into expressions, and each `c = value` is proved by kernel evaluation in its own declaration (fresh
  kernel caches); the decided term is then evaluated over the values, bridged by congruence. Values are
  untrusted hints: only kernel-checked equations enter the proof. -/
  stage : Bool := false
  /-- Heartbeat limit (thousands) of each staged equation `c = value`; `0` = none. -/
  stageHeartbeats : Nat := 60000
  /-- Most staged equations per fact (constants and subterms). -/
  stageMax : Nat := 4096
  /-- A part whose compiled evaluation takes at least this many milliseconds is decomposed before any
  attempt to check it as a whole (the kernel is several orders of magnitude slower). -/
  stageNativeMs : Nat := 50
  /-- Largest value (expression nodes) that is staged. -/
  stageSize : Nat := 4000000
  /-- Register the staged equations globally, so that modules importing this one reuse them (a module
  that only stages shared constants serves every fact of a package). -/
  stageGlobal : Bool := false
  /-- Also stage closed subterms of the decided term (not only data constants). -/
  stageSubterms : Bool := true
  /-- How many times a staged part may be decomposed further (chunks, subterms, unfolding; a recursion
  peeled one call at a time uses one level per call). -/
  stageDepth : Nat := 32
  /-- Passed to the copier (`CopyConfig.csimp`): `@[csimp]` replacements of Mathlib and of the project
  (e.g. `Nat.choose = fast_choose`) are used as kernel replacements. -/
  csimp : Bool := false
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
def findBlockers (e : Expr) (static : Bool := false) (skipProofs : Bool := false)
    (retryRepl : Bool := false) : CoreM (Array Blocker) := do
  let env ← getEnv
  -- `static` with `retryRepl`: as the retry's copies would have them (`@[kernel_fold]` patterns folded,
  -- `@[kernel_replace_retry]` replacements followed)
  let user := if static && retryRepl then
      (kernelRetryReplaceExt.getState env).foldl (fun m f r => m.insert f r) (kernelReplaceExt.getState env)
    else kernelReplaceExt.getState env
  let fold (b : Expr) (self : Name := .anonymous) : Expr :=
    if static && retryRepl then foldApps env b self else b
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  let mut out : Array Blocker := #[]
  for c in (fold e).getUsedConstants do
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
      for dep in (if static || !skipProofs then (fold d.value c).getUsedConstants else relevantConsts env d.value) do
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

/-- Explain why the kernel did not prove `e' = true`; also returns the stuck point found by
`findStuck`, if the evaluation got stuck (used by the cast retry, `castRetryReps`). -/
def diagnose (e' : Expr) (lvls : List Name) (kernelEx : Exception) (native? : Option Bool)
    (cfg : KernelConfig) : MetaM (MessageData × Option (Expr × Option Name)) := do
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
    return (msg, none)
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
  return (msg, stuck)

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
`native?` is the result of compiled evaluation, if known (used in diagnostics only). `castReps` are
cast-free versions to use like registered replacements (the cast retry); on a failed evaluation, the
stuck point found by the diagnosis is stored in `stuckOut`. -/
def proveTrueByKernelCore (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) (castReps : Array (Name × Name × Name) := #[])
    (stuckOut : Option (IO.Ref (Option (Expr × Option Name))) := none) : MetaM KernelResult := do
  -- functions applied to long string literals (`@[kernel_string_arg]`): `sPf? : e = e₀`
  let (e₀, sPf?) ← match ← strArgSubst e (mkConst ``Bool) cfg.fastLitMin with
    | some (h, v) => pure (v, some h)
    | none => pure (e, none)
  -- the retry with retry-only replacements: `@[kernel_fold]` patterns in the decided term, definitionally
  -- equal, so the bridges below are checked against `e` up to this unfolding
  let envFold ← getEnv
  let e₀ := if cfg.retryRepl then foldApps envFold e₀ else e₀
  -- reachable blockers: bounded evaluation (see `KernelConfig.blockedHeartbeats`)
  let t0 ← IO.monoMsNow
  let bounded ← if cfg.blockedHeartbeats != 0 &&
      (cfg.maxHeartbeats == 0 || cfg.maxHeartbeats > cfg.blockedHeartbeats) then do
      pure !(← findBlockers e₀ (static := cfg.wf) (retryRepl := cfg.retryRepl)).isEmpty
    else pure false
  -- registered replacements always apply; `cfg.wf` only controls the `WellFounded.fix` transform
  let t1 ← IO.monoMsNow
  -- copies made with cast-free versions are named after the set of them (and the route)
  let castTag : Name := if castReps.isEmpty then .anonymous else
    let h := castReps.foldl (fun h (c, c', _) => mixHash h (mixHash (hash c) (hash c'))) (7 : UInt64)
    Name.mkSimple s!"_ktc{h.toNat % 100000000}{if cfg.transport then "t" else ""}"
  let ccfg : CopyConfig := { opt := cfg.opt, wf := cfg.wf, wfAcc := cfg.wfAcc, trace := cfg.trace, skipUnchanged := cfg.skipUnchanged, transport := cfg.transport, fastLitMin := cfg.fastLitMin, castReps, castTag, keepTypes := cfg.keepTypes, retryRepl := cfg.retryRepl, deadline := cfg.retryDeadline, copyHeartbeats := if cfg.retryRepl then cfg.retryHeartbeats else if cfg.transport then cfg.transportHeartbeats else 0, csimp := cfg.csimp }
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
    let (msg₀, stuck) ← diagnose e' lvls ex native? cfg
    if let some ref := stuckOut then ref.set stuck
    let mut msg := msg₀
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

/-- One attempt (`proveTrueByKernelCore`); when it fails stuck at a cast, cast-free versions of the
definitions concerned (`castRetryReps`) and one more attempt with them (`KernelConfig.castRetry`; up to
`castRounds` such retries, each adding the definitions at whose cast the previous one got stuck). If
the retries fail too, the first attempt's error is rethrown (the retries' go to the trace), so the
routes after it run as before. -/
def attemptWithCastRetry (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  let stuckRef ← IO.mkRef none
  try proveTrueByKernelCore e name lvls cfg native? #[] (some stuckRef)
  catch ex =>
    unless cfg.castRetry do throw ex
    let mut reps : Array (Name × Name × Name) := #[]
    for _ in [0:cfg.castRounds] do
      let some (stuck, via?) ← stuckRef.get | break
      let new ← try castRetryReps stuck via? cfg.searchHeartbeats cfg.trace (reps.map (·.1)) catch _ => pure #[]
      if new.isEmpty then break
      reps := reps ++ new
      if cfg.trace then
        eprintRaw s!"NT {name} cast-retry {reps.toList.map fun (c, c', _) => s!"{c} ↦ {c'}"}"
      stuckRef.set none
      try return ← proveTrueByKernelCore e name lvls cfg native? reps (some stuckRef)
      catch exRetry =>
        if cfg.trace then
          let m := (← exRetry.toMessageData.toString).replace "\n" " "
          eprintRaw s!"NT {name} cast-retry-failed {m.take 400}"
    throw ex

/-- The parametric route (`NativeTrust.Param`): every definition between the decided term and the replaced
constants, types included, is rewritten over variables for the replaced constants (`E F h`). The kernel
proves `e = E r rfl` by unfolding, `E r rfl = E r' hᵣ` by dependent congruence (one replaced constant at a
time), and evaluates `E r' hᵣ` (with `fixFuel`) to `true`. -/
def proveTrueByKernelParamCore (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) (castReps : Array (Name × Name × Name) := #[])
    (stuckOut : Option (IO.Ref (Option (Expr × Option Name))) := none) : MetaM KernelResult := do
  let t1 ← IO.monoMsNow
  let ccfg : CopyConfig := { wf := cfg.wf, trace := cfg.trace, fastLitMin := 0, retryRepl := cfg.retryRepl, copyHeartbeats := if cfg.retryRepl then cfg.retryHeartbeats else 0 }
  let envEval ← getEnv
  try
    let pt ← Param.paramTerm e ccfg castReps
    let n := pt.origs.size
    if n == 0 then throwError "NativeTrust: parametric route: no replaced constant is reachable"
    let args (xs hs : Array Expr) : Array Expr :=
      (Array.range n).foldl (fun acc i => (acc.push xs[i]!).push hs[i]!) #[]
    let e' := pt.E.beta (args pt.repls pt.eqs)
    let t2 ← IO.monoMsNow
    if cfg.trace then
      eprintRaw s!"NT {name} param roots={n} gens={pt.created.size} gen_errors={pt.errors.size} ms={t2 - t1}"
    -- bounded like the fuel route when constants without a kernel definition are reachable
    let bounded ← if cfg.blockedHeartbeats != 0 &&
        (cfg.maxHeartbeats == 0 || cfg.maxHeartbeats > cfg.blockedHeartbeats) then do
        pure !(← findBlockers e (static := cfg.wf)).isEmpty
      else pure false
    let cfg := if bounded then { cfg with maxHeartbeats := cfg.blockedHeartbeats } else cfg
    let evalName := name ++ `eval
    let ms ← match ← tryAddTheorem evalName lvls (mkBoolEq e' boolTrue) (reflBool boolTrue) cfg with
      | .ok ms => pure ms
      | .error ex =>
        let (msg₀, stuck₀) ← diagnose e' lvls ex native? cfg
        -- the static blocker analysis sees `WellFounded.fix` in the types of the root variables of the
        -- generic definitions, so `diagnose` may skip `findStuck`: look for a stuck cast directly
        let stuck ← if stuck₀.isSome then pure stuck₀ else
          if (← ex.toMessageData.toString).contains "type mismatch" then
            (try findStuck e' catch _ => pure none)
          else pure none
        if let some ref := stuckOut then ref.set stuck
        let mut msg := msg₀
        unless pt.errors.isEmpty do
          msg := msg ++ m!"\n\nParametric route: definitions without a generic version:\n" ++
            MessageData.joinSep (pt.errors.toList.take 5) "\n"
        throwError msg
    -- `e = E r rfl` (unfolding; in the retry from the equations of the generic versions, `pt.bridge?`), then
    -- dependent congruence along each root's equation
    let boolT := mkConst ``Bool
    let mut proof := pt.bridge?.getD (mkApp2 (mkConst ``Eq.refl [1]) boolT e)
    let mut curX := pt.origs
    let mut curH := pt.rfls
    let mut lhs := pt.E.beta (args pt.origs pt.rfls)
    for i in [0:n] do
      let (cx, ch) := (curX, curH)
      let eqTo (t : Expr) := mkApp3 (mkConst ``Eq [pt.levels[i]!]) pt.types[i]! pt.origs[i]! t
      let Fi ← withLocalDeclD `y pt.types[i]! fun y => withLocalDeclD `hy (eqTo y) fun hy =>
        mkLambdaFVars #[y, hy] (pt.E.beta (args (cx.set! i y) (ch.set! i hy)))
      let step := mkAppN (mkConst ``NativeTrust.congr_dep [pt.levels[i]!, 1])
        #[pt.types[i]!, boolT, pt.origs[i]!, Fi, pt.repls[i]!, pt.eqs[i]!]
      curX := curX.set! i pt.repls[i]!
      curH := curH.set! i pt.eqs[i]!
      let rhs := pt.E.beta (args curX curH)
      proof := mkApp6 (mkConst ``Eq.trans [1]) boolT e lhs rhs proof step
      lhs := rhs
    let evalThm := mkConst evalName (lvls.map mkLevelParam)
    let full := mkApp6 (mkConst ``Eq.trans [1]) boolT e e' boolTrue proof evalThm
    if let .error ex ← tryAddTheorem name lvls (mkBoolEq e boolTrue) full cfg then
      throwError m!"NativeTrust internal error: the kernel rejected the bridge of the parametric \
        route:\n{ex.toMessageData}"
    if cfg.trace then eprintRaw s!"NT {name} eval_ms={ms}"
    let axs ← collectAxioms name
    let bad := axs.filter (!stdAxioms.contains ·)
    unless bad.isEmpty do
      throwError m!"NativeTrust: the kernel proof uses non-standard axioms {bad.toList}"
    return { thm := name, copies := pt.created, ms }
  catch ex =>
    setEnv envEval
    throw ex

/-- The parametric route, with the cast retry of `attemptWithCastRetry`: when the evaluation gets stuck
at a cast, cast-free versions of the definitions concerned (`castRetryReps`) become roots too, and the
route runs again (up to `max castRounds 3` times: a cast-free version can uncover the cast of a
definition it calls). Definitions that occur in types are often reached by evaluation only once they are
rewritten, so their casts show up here first. -/
partial def proveTrueByKernelParam (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  let rec go (round : Nat) (reps : Array (Name × Name × Name)) (first? : Option Exception) :
      MetaM KernelResult := do
    let stuckRef ← IO.mkRef none
    try proveTrueByKernelParamCore e name lvls cfg native? reps (some stuckRef)
    catch ex =>
      let first := first?.getD ex
      unless cfg.castRetry && round < max cfg.castRounds 3 do throw first
      let some (stuck, via?) ← stuckRef.get | throw first
      let new ← try castRetryReps stuck via? cfg.searchHeartbeats cfg.trace (reps.map (·.1))
        catch _ => pure #[]
      if new.isEmpty then throw first
      let reps := reps ++ new
      if cfg.trace then
        eprintRaw s!"NT {name} param-cast-retry {reps.toList.map fun (c, c', _) => s!"{c} ↦ {c'}"}"
      go (round + 1) reps (some first)
  go 0 #[] none

/-- `tryAddTheorem` in a throwaway environment, without the messages it logs (a `sorry` warning), with the
heartbeats it took, as `IO.getNumHeartbeats` counts them. -/
def probeTheorem (name : Name) (lvls : List Name) (type value : Expr) (cfg : KernelConfig) :
    CoreM (Except Exception Nat) := do
  let msgs := (← get).messages
  let hb0 ← IO.getNumHeartbeats
  let r ← withoutModifyingEnv <| tryAddTheorem name lvls type value cfg
  let hb := (← IO.getNumHeartbeats) - hb0
  modify fun s => { s with messages := msgs }
  return r.map fun _ => hb

/-- Did a kernel check run out of heartbeats? -/
def isHeartbeatError (ex : Exception) : CoreM Bool := do
  let msg ← ex.toMessageData.toString
  return (msg.splitOn "deterministic timeout").length > 1 || (msg.splitOn "heartbeats").length > 1

/-- The smaller of two heartbeat limits, where `0` means no limit. -/
def minHeartbeats (a b : Nat) : Nat := if a == 0 then b else if b == 0 then a else min a b

/-- The platform case split, a retry for terms that reach `System.Platform.getNumBits` (`USize` arithmetic,
hence `HashMap`/`HashSet` indices). In the logic the word size is unknown, but it is 32 or 64
(`System.Platform.numBits_eq`). The parametric route makes `System.Platform.numBits` a root, and the kernel
evaluates the generic term at `numBits := 32` and at `numBits := 64`, each under the hypothesis
`h : numBits = v`, which evaluation never needs (it occurs only in proofs). `Or.elim` on `numBits_eq` and
dependent congruence along `h` give `e = true`. A result that depends on the platform (the iteration order of a
hash map, say) need not evaluate to `true` at both, and is then not proved. The retry-only replacements are
roots as well.

With `h` free, the kernel computes `Nat` arithmetic step by step (it uses its fast arithmetic on literals only in
terms without free variables), so arithmetic on large numbers can take practically forever. Each case is
therefore first checked with `h` replaced by a closed stand-in, in a throwaway environment (`probeTheorem`): if
that does not reduce to `true`, the case fails at once (saying whether it reduces to `false`: then the result
depends on the word size); if it does, the evaluation with `h` free gets at most `platformSlowdown` times its work
(at least `blockedHeartbeats`) and fails beyond that. Every evaluation with `h` free is also limited to
`platformHeartbeats`.

The check with the stand-in is a pre-check only: it decides whether and how long to evaluate, nothing from it
enters a proof or the environment (it runs in a throwaway environment and its messages are discarded), so what
the result trusts does not change. The proof consists of the evaluations with `h` free and the congruences. -/
def proveTrueByKernelPlatformCore (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (castReps : Array (Name × Name × Name) := #[])
    (stuckOut : Option (IO.Ref (Option (Expr × Option Name))) := none) : MetaM KernelResult := do
  let t1 ← IO.monoMsNow
  let ccfg : CopyConfig := { wf := cfg.wf, trace := cfg.trace, fastLitMin := 0, retryRepl := true, copyHeartbeats := cfg.retryHeartbeats }
  let envEval ← getEnv
  try
    let pt ← Param.paramTerm e ccfg (#[(``System.Platform.numBits, ``System.Platform.numBits, ``Param.numBits_refl)] ++ castReps)
    let n := pt.origs.size
    let some j := pt.origs.findIdx? (·.isConstOf ``System.Platform.numBits)
      | throwError "NativeTrust: platform case split: `System.Platform.numBits` is not reachable"
    let nb := mkConst ``System.Platform.numBits
    let natT := mkConst ``Nat
    let boolT := mkConst ``Bool
    let nbEq (v : Expr) := mkApp3 (mkConst ``Eq [1]) natT nb v
    let args (xs hs : Array Expr) : Array Expr :=
      (Array.range n).foldl (fun acc i => (acc.push xs[i]!).push hs[i]!) #[]
    if cfg.trace then
      eprintRaw s!"NT {name} platform roots={n} gens={pt.created.size} gen_errors={pt.errors.size} ms={(← IO.monoMsNow) - t1}"
    -- bounded like the fuel route when constants without a kernel definition are reachable, other than the
    -- word size, which the case split supplies
    let bounded ← if cfg.blockedHeartbeats != 0 &&
        (cfg.maxHeartbeats == 0 || cfg.maxHeartbeats > cfg.blockedHeartbeats) then do
        pure ((← findBlockers e (static := cfg.wf)).any (·.name != ``System.Platform.getNumBits))
      else pure false
    let cfgE := if bounded then { cfg with maxHeartbeats := cfg.blockedHeartbeats } else cfg
    -- every root but `numBits` at its replacement
    let xs := pt.repls.set! j nb
    let hs := pt.eqs.set! j (mkApp2 (mkConst ``Eq.refl [1]) natT nb)
    -- `∀ h : numBits = v, E … v h … = true`, by evaluation
    let mut evals := #[]
    let mut ms := 0
    let mut probeOver := false
    for v in [32, 64] do
      let (ty, val) ← withLocalDeclD `h (nbEq (mkNatLit v)) fun h => do
        let ev := pt.E.beta (args (xs.set! j (mkNatLit v)) (hs.set! j h))
        return (← mkForallFVars #[h] (mkBoolEq ev boolTrue), ← mkLambdaFVars #[h] (reflBool boolTrue))
      let evalName := name ++ Name.mkSimple s!"eval{v}"
      -- the case with the hypothesis replaced by a closed stand-in: a pre-check only, checked in a throwaway
      -- environment; nothing from it enters a proof or the environment, so trust does not change
      let stand := mkApp2 (mkConst ``sorryAx [levelZero]) (nbEq (mkNatLit v)) (mkConst ``Bool.false)
      let evS := pt.E.beta (args (xs.set! j (mkNatLit v)) (hs.set! j stand))
      let recordStuck : MetaM Unit := do
        -- the stuck point, for the cast retry (`proveTrueByKernelPlatform`)
        if let some ref := stuckOut then
          ref.set (← try findStuck evS 300000 catch _ => pure none)
      let mut cfgV := cfgE
      let mut capped := false
      if cfg.platformProbeHeartbeats != 0 && !probeOver then
        let probeCfg := { cfgE with maxHeartbeats := minHeartbeats cfgE.maxHeartbeats cfg.platformProbeHeartbeats }
        match ← probeTheorem (name ++ Name.mkSimple s!"probe{v}") lvls (mkBoolEq evS boolTrue) (reflBool boolTrue)
            probeCfg with
        | .ok hb =>
          let cap := minHeartbeats cfgE.maxHeartbeats (max cfg.blockedHeartbeats (cfg.platformSlowdown * hb / 1000 + 1))
          cfgV := { cfgE with maxHeartbeats := cap }
          capped := true
          if cfg.trace then eprintRaw s!"NT {name} platform probe{v} ok hb={hb} cap={cfgV.maxHeartbeats}"
        | .error ex =>
          if ← isHeartbeatError ex then
            probeOver := true
            if cfg.trace then eprintRaw s!"NT {name} platform probe{v} over budget"
          else
            -- it does not reduce to `true` even with the stand-in, so it does not with `h` free either
            if let .ok _ ← probeTheorem (name ++ Name.mkSimple s!"probeFalse{v}") lvls (mkBoolEq evS boolFalse)
                (reflBool boolFalse) probeCfg then
              throwError m!"NativeTrust: platform case split: at numBits = {v} the term evaluates to `false`: \
                its result depends on the word size"
            recordStuck
            let msg ← ex.toMessageData.toString
            let first := (msg.splitOn "\n").headD ""
            let detail := if (first.splitOn "type mismatch").length > 1 then "" else s!": {first.take 200}"
            throwError m!"NativeTrust: platform case split: at numBits = {v} the term does not reduce to \
              `true`, nor to `false` (its evaluation gets stuck{detail})"
      -- the hard limit, whatever the pre-check showed
      let limited := cfg.platformHeartbeats != 0 &&
        (cfgV.maxHeartbeats == 0 || cfg.platformHeartbeats < cfgV.maxHeartbeats)
      if limited then cfgV := { cfgV with maxHeartbeats := cfg.platformHeartbeats }
      match ← tryAddTheorem evalName lvls ty val cfgV with
      | .ok t =>
        ms := ms + t
        evals := evals.push (mkConst evalName (lvls.map mkLevelParam))
      | .error ex =>
        if (capped || limited) && (← isHeartbeatError ex) then
          if capped && !limited then
            throwError m!"NativeTrust: platform case split: at numBits = {v} the term reduces to `true` with the \
              hypothesis `numBits = {v}` replaced by a closed stand-in, but not within {cfgV.maxHeartbeats} \
              thousand heartbeats with it free: Lean's kernel uses its fast arithmetic on literals only in \
              terms without free variables, and computes `Nat` arithmetic on large numbers step by step"
          throwError m!"NativeTrust: platform case split: the evaluation at numBits = {v} did not finish within \
            {cfgV.maxHeartbeats} thousand heartbeats (`platformHeartbeats`; with the hypothesis `numBits = {v}` \
            free, Lean's kernel computes `Nat` arithmetic on large numbers step by step)"
        recordStuck
        throwError m!"NativeTrust: platform case split: the evaluation at numBits = {v} failed:\n{ex.toMessageData}"
    -- `e = E r rfl`, then every root but `numBits` along its equation to its replacement
    let mut proof := pt.bridge?.getD (mkApp2 (mkConst ``Eq.refl [1]) boolT e)
    let mut curX := pt.origs
    let mut curH := pt.rfls
    let mut lhs := pt.E.beta (args pt.origs pt.rfls)
    for i in [0:n] do
      if i == j then continue
      let (cx, ch) := (curX, curH)
      let eqTo (t : Expr) := mkApp3 (mkConst ``Eq [pt.levels[i]!]) pt.types[i]! pt.origs[i]! t
      let Fi ← withLocalDeclD `y pt.types[i]! fun y => withLocalDeclD `hy (eqTo y) fun hy =>
        mkLambdaFVars #[y, hy] (pt.E.beta (args (cx.set! i y) (ch.set! i hy)))
      let step := mkAppN (mkConst ``NativeTrust.congr_dep [pt.levels[i]!, 1])
        #[pt.types[i]!, boolT, pt.origs[i]!, Fi, pt.repls[i]!, pt.eqs[i]!]
      curX := curX.set! i pt.repls[i]!
      curH := curH.set! i pt.eqs[i]!
      let rhs := pt.E.beta (args curX curH)
      proof := mkApp6 (mkConst ``Eq.trans [1]) boolT e lhs rhs proof step
      lhs := rhs
    -- per case: `numBits` along `h : numBits = v`, then the evaluation
    let mut cases := #[]
    for (v, k) in [(32, 0), (64, 1)] do
      let c ← withLocalDeclD `h (nbEq (mkNatLit v)) fun h => do
        let Fj ← withLocalDeclD `y natT fun y => withLocalDeclD `hy (nbEq y) fun hy =>
          mkLambdaFVars #[y, hy] (pt.E.beta (args (curX.set! j y) (curH.set! j hy)))
        let step := mkAppN (mkConst ``NativeTrust.congr_dep [1, 1]) #[natT, boolT, nb, Fj, mkNatLit v, h]
        let rhs := pt.E.beta (args (curX.set! j (mkNatLit v)) (curH.set! j h))
        let p1 := mkApp6 (mkConst ``Eq.trans [1]) boolT e lhs rhs proof step
        mkLambdaFVars #[h] (mkApp6 (mkConst ``Eq.trans [1]) boolT e rhs boolTrue p1 (mkApp evals[k]! h))
      cases := cases.push c
    let target := mkBoolEq e boolTrue
    let full := mkAppN (mkConst ``Or.elim)
      #[nbEq (mkNatLit 32), nbEq (mkNatLit 64), target, mkConst ``System.Platform.numBits_eq, cases[0]!, cases[1]!]
    if let .error ex ← tryAddTheorem name lvls target full cfg then
      throwError m!"NativeTrust internal error: the kernel rejected the bridge of the platform case split:\n{ex.toMessageData}"
    if cfg.trace then eprintRaw s!"NT {name} platform eval_ms={ms}"
    let axs ← collectAxioms name
    let bad := axs.filter (!stdAxioms.contains ·)
    unless bad.isEmpty do
      throwError m!"NativeTrust: the kernel proof uses non-standard axioms {bad.toList}"
    return { thm := name, copies := pt.created, ms }
  catch ex =>
    setEnv envEval
    throw ex

/-- `proveTrueByKernelPlatformCore` with the cast retry of the parametric route: when an evaluation gets stuck at
a cast, cast-free versions of the definitions concerned become roots too (a derived `DecidableEq` of a structure
with a function field, say, which `HashSet` code reaches only once the word size is known). -/
partial def proveTrueByKernelPlatform (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig) :
    MetaM KernelResult := do
  let rec go (round : Nat) (reps : Array (Name × Name × Name)) (first? : Option Exception) :
      MetaM KernelResult := do
    let stuckRef ← IO.mkRef none
    try proveTrueByKernelPlatformCore e name lvls cfg reps (some stuckRef)
    catch ex =>
      let first := first?.getD ex
      unless cfg.castRetry && round < max cfg.castRounds 3 do throw first
      let some (stuck, via?) ← stuckRef.get | throw first
      let new ← try castRetryReps stuck via? cfg.searchHeartbeats cfg.trace (reps.map (·.1))
        catch _ => pure #[]
      if new.isEmpty then throw first
      let reps := reps ++ new
      if cfg.trace then
        eprintRaw s!"NT {name} platform-cast-retry {reps.toList.map fun (c, c', _) => s!"{c} ↦ {c'}"}"
      go (round + 1) reps (some first)
  -- cast-free versions made earlier in this module (by the other pieces of a structured check, say) are
  -- used from the start; a root that `e` does not reach is not abstracted
  let env ← getEnv
  let pre ← castFreePrefix
  let existing := env.constants.map₂.toList.filterMap fun (c', _) =>
    if pre.isPrefixOf c' && !(c'.isStr && c'.getString! == "_eq") && env.contains (c' ++ `_eq) then
      let c := c'.replacePrefix pre .anonymous
      if env.contains c then some (c, c', c' ++ `_eq) else none
    else none
  go 0 existing.toArray none

/-- Is a `@[kernel_fold]` pattern head or a `@[kernel_replace_retry]` replacement reachable from `e`
through definition bodies, as the default routes see them (nothing folded)? Decides whether the retry
with retry-only replacements can change anything. -/
def retryReplReachable (e : Expr) : CoreM Bool := do
  let env ← getEnv
  let folds := foldExt.getState env
  let retry := kernelRetryReplaceExt.getState env
  if folds.isEmpty && retry.isEmpty then return false
  let user := kernelReplaceExt.getState env
  let mut seen : NameSet := {}
  let mut todo := e.getUsedConstants
  while h : 0 < todo.size do
    let c := todo.back
    todo := todo.pop
    if seen.contains c then continue
    seen := seen.insert c
    if folds.contains c || retry.contains c then return true
    if let some (g, _) := user.find? c then
      todo := todo.push g
      continue
    if let some (.defnInfo d) := env.find? c then
      todo := todo ++ d.value.getUsedConstants
  return false


/-- `proveTrueByKernelCore` with the fuel route, and the accessibility-generator route as a
fallback when well-founded recursion is what stops the fuel route (`KernelConfig.accFallback`). The
first attempt and the fuel route's retry each retry once with cast-free versions of the definitions
whose casts stop the evaluation (`attemptWithCastRetry`); the retry also keeps type formers as they are
(`keepTypes`). Before the fallback, the parametric route (`KernelConfig.param`,
`proveTrueByKernelParam`) handles definitions that occur in types. Right after the first attempt comes
the attempt with the retry-only replacements (`KernelConfig.foldRetry`, see `proveTrueByKernel`). -/
def proveTrueByKernelRoutes (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) (retryErr : Option (IO.Ref (Option MessageData)) := none) :
    MetaM KernelResult := do
  try attemptWithCastRetry e name lvls cfg native?
  catch ex =>
    -- the retry with retry-only replacements (`KernelConfig.foldRetry`), right after the first attempt:
    -- the routes below can cost far more than it on the facts it is for (iterator-based `String` code),
    -- and every fact the first attempt converts is converted exactly as before
    if cfg.foldRetry && !cfg.retryRepl && (← retryReplReachable e) then
      if cfg.trace then eprintRaw s!"NT {name} retry-repl"
      let deadline := (← IO.monoMsNow) + cfg.retryMs
      try
        return (← attemptWithCastRetry e name lvls { cfg with retryRepl := true, retryDeadline := deadline } native?)
      catch exRetry =>
        if let some ref := retryErr then ref.set (some exRetry.toMessageData)
        if cfg.trace then
          -- one line, and no backquotes: a truncated name in backquotes would run into later log lines
          let m := ((← exRetry.toMessageData.toString).replace "\n" " ").replace "`" "'"
          eprintRaw s!"NT {name} retry-repl-failed {m.take 600}"
        -- the parametric route with the retry-only replacements as roots: definitions that reach a
        -- replaced `String` function and occur in types (a `match h : f x with` whose `h` a structure stores)
        if cfg.param && cfg.paramRetryRepl then
          if cfg.trace then eprintRaw s!"NT {name} retry-repl-param"
          try
            return (← proveTrueByKernelParam e name lvls { cfg with retryRepl := true, retryDeadline := deadline } native?)
          catch exP =>
            if cfg.trace then
              let m := ((← exP.toMessageData.toString).replace "\n" " ").replace "`" "'"
              eprintRaw s!"NT {name} retry-repl-param-failed {m.take 600}"
    -- the platform case split: `USize` arithmetic (hash maps and sets) at word size 32 and at 64; after the
    -- routes below when they apply, so that every fact they convert is converted as before
    let blockers ← if cfg.platformCases && !cfg.retryRepl then findBlockers e (static := true) else pure #[]
    let platformErr ← IO.mkRef (none : Option MessageData)
    let platform : MetaM (Option KernelResult) := do
      unless blockers.any (·.name == ``System.Platform.getNumBits) do return none
      if cfg.trace then eprintRaw s!"NT {name} platform-cases"
      try
        return some (← proveTrueByKernelPlatform e name lvls cfg)
      catch exP =>
        platformErr.set (some exP.toMessageData)
        if cfg.trace then
          let m := ((← exP.toMessageData.toString).replace "\n" " ").replace "`" "'"
          eprintRaw s!"NT {name} platform-cases-failed {m.take 600}"
        return none
    -- the report: the first attempt's error, and the case split's when it was tried
    let withPlatform (m : MessageData) : MetaM MessageData := do
      match ← platformErr.get with
      | some mp => return m!"{m}\n\nRetried with the platform case split (`numBits = 32 ∨ numBits = 64`), \
          which failed too:\n{mp}"
      | none => return m
    let fail : MetaM KernelResult := do
      if (← platformErr.get).isNone then throw ex
      throwError (← withPlatform ex.toMessageData)
    let wfReachable := cfg.wf && !cfg.wfAcc && (← findBlockers e).any (·.name == ``WellFounded.fix)
    unless wfReachable do
      if let some r ← platform then return r
    unless cfg.wf && !cfg.wfAcc do return ← fail
    -- only when well-founded recursion is reachable at all
    unless wfReachable do return ← fail
    -- the fuel route once more, with the proofs inside rejected copies transported along the copy
    -- equations and unchanged copies skipped (own copy names): a retry, so that every fact the
    -- first attempt converts is converted exactly as before
    if !cfg.transport then
      if cfg.trace then eprintRaw s!"NT {name} fuel-retry-transport"
      try
        return (← attemptWithCastRetry e name lvls { cfg with transport := true, skipUnchanged := true, keepTypes := true } native?)
      catch exRetry =>
        -- the report below shows the first attempt's error; the retry's goes to the trace
        if cfg.trace then
          let m := (← exRetry.toMessageData.toString).replace "\n" " "
          eprintRaw s!"NT {name} fuel-retry-failed {m.take 400}"
    -- the parametric route, for definitions that occur in types
    if cfg.param && !cfg.transport then
      if cfg.trace then eprintRaw s!"NT {name} param-route"
      try
        return (← proveTrueByKernelParam e name lvls cfg native?)
      catch exParam =>
        if cfg.trace then
          let m := (← exParam.toMessageData.toString).replace "\n" " "
          eprintRaw s!"NT {name} param-failed {m.take 600}"
    if let some r ← platform then return r
    unless cfg.accFallback do return ← fail
    if cfg.trace then eprintRaw s!"NT {name} acc-fallback"
    try proveTrueByKernelCore e name lvls { cfg with wfAcc := true } native?
    catch ex' =>
      -- report both: the retry can fail for another reason than the fuel route
      throwError (← withPlatform m!"{ex.toMessageData}\n\nRetried with the accessibility-generator route \
        (`wfAcc`), which failed too:\n{ex'.toMessageData}")

/-- `proveTrueByKernelRoutes`: the first attempt (with the cast retry), then, when a `@[kernel_fold]`
pattern or a `@[kernel_replace_retry]` replacement is reachable, one attempt with them (`KernelConfig.foldRetry`;
for instance the `String` functions of `NativeTrust.StrLib`), then the fuel route's retry, the parametric
route, the platform case split when `System.Platform.getNumBits` is reachable (`proveTrueByKernelPlatform`; before
the fuel route's retry when that does not apply) and the accessibility-generator fallback. The first attempt never sees the retry-only replacements,
so every fact it converts is converted exactly as without them; their attempt copies under a time budget
(`retryMs`) with bounded kernel checks (`retryHeartbeats`), because it can have to copy much of what
reaches a `String` function. If everything fails, the report adds the retry's error. -/
def proveTrueByKernel (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  let retryErr ← IO.mkRef none
  try proveTrueByKernelRoutes e name lvls cfg native? (some retryErr)
  catch ex =>
    match ← retryErr.get with
    | some m => throwError m!"{ex.toMessageData}\n\nRetried with the retry-only replacements \
        (`@[kernel_fold]`, `@[kernel_replace_retry]`, e.g. `NativeTrust.StrLib`) after the first attempt, \
        which failed too:\n{m}"
    | none => throw ex

/-! ## Staged evaluation: shared intermediate lemmas

A check whose cost is one large computation (an equality or comparison of computed values) has no
logical structure to split, and the kernel's caches grow with the evaluation inside one declaration.
Its intermediate values can still be proved separately:

1. compiled code evaluates an expensive closed part `t` of the computation, and `reifyValue` turns the
   value into an expression `v` (an untrusted hint);
2. `t = c_v` (`c_v := v`) is proved by kernel evaluation in its own declaration, so with fresh kernel
   caches, over the values staged before it;
3. a staged constant is registered as a replacement `c ↦ c_v`: `kernelCopy` rebuilds the definitions
   that reach it and bridges them by congruence, as for every replacement, and the decided term is
   finally evaluated over the values.

What is staged: the data constants reachable from the decided term (tables, parsed data, points built
by field arithmetic; not constants reached from types), then the closed subterms of the decided term
(the sides of an equality, nested calls) as `abbrev` auxiliary constants. A part whose equation does not
check within `stageHeartbeats` (or whose compiled evaluation took `stageNativeMs` or more) is decomposed
and its pieces are staged first:
* a list literal (long ones elaborate to `have` chains, which are zeta-reduced) in chunks;
* `List.map f l`, `List.foldl f b l` and `List.foldr f b l` over a list of known value, in chunks
  (`List.foldl_append`, `List.foldr_append`; the accumulators are staged in order);
* the closed subterms of its body;
* a projection of a computed structure, reduced after unfolding the structure to a constructor;
* one unfolding of the head (`f.eq_def` when `f` is recursive, delta otherwise), followed by the
  reduction of matches on constructor-headed values.
Each step is an equation that the kernel checks cheaply: an unfolding, a match reduction proved with
the alternatives abstracted (so the kernel cannot evaluate them), congruence from `sᵢ = aᵢ` for the
auxiliary constants and from the staged equations, or the unfolding of appends of literals. The kernel
never compares two large terms as a whole. A wrong value only makes its equation fail. -/

/-- Is `e` already a value: literals, constructor applications (types and proofs as arguments),
`OfNat.ofNat` of a raw literal, or a staged value constant (`_ktval`)? Bounded; `false` when unsure. -/
partial def isValueLike (e : Expr) (budget : Nat := 200000) : MetaM Bool := do
  let env ← getEnv
  let fuel ← IO.mkRef budget
  let rec go (e : Expr) : MetaM Bool := do
    let n ← fuel.get
    if n == 0 then return false
    fuel.set (n - 1)
    match e with
    | .lit _ | .sort _ => return true
    | .mdata _ b => go b
    | .const c _ => return (c.components.contains `_ktval) ||
        (env.find? c matches some (.ctorInfo _)) || (env.find? c matches some (.inductInfo _))
    | _ =>
      let .const c _ := e.getAppFn | return false
      if c == ``OfNat.ofNat && e.getAppNumArgs == 3 then return (e.getArg! 1).isRawNatLit
      match env.find? c with
      | some (.ctorInfo ci) =>
        let args := e.getAppArgs
        for i in [ci.numParams:args.size] do
          let a := args[i]!
          if ← (try isProof a catch _ => pure false) then continue
          unless ← go a do return false
        return true
      | some (.inductInfo _) => return true
      | _ => return false
  go e

/-- Constructor-headed (an application of a constructor, a literal, or a staged value constant): enough
for a match on it to take a branch (deeper patterns are checked by the kernel). -/
def isCtorHeaded (e : Expr) : MetaM Bool := do
  let env ← getEnv
  match e.getAppFn with
  | .lit _ => return true
  | .const c _ =>
    if c.components.contains `_ktval then return true
    if c == ``OfNat.ofNat && e.getAppNumArgs == 3 then return (e.getArg! 1).isRawNatLit
    return (env.find? c matches some (.ctorInfo _))
  | _ => return false

/-- Data that staging can prove equal to a value: not a function, type, proposition or class, and
reifiable. -/
def isStageType (T : Expr) : MetaM Bool := do
  if T.hasLooseBVars || T.hasFVar || T.hasMVar then return false
  try
    let T' ← whnf T
    if T'.isForall || T'.isSort then return false
    if ← isProp T then return false
    if (← isClass? T).isSome then return false
    reifiable T
  catch _ => return false

/-- The constants of `e` outside proofs, and separately those inside types: binder types and the type
arguments of applications (by the binder types of the applied constant). -/
partial def valueConsts (env : Environment) (e : Expr) : Array Name × Array Name := Id.run do
  let mut out : Array Name := #[]
  let mut tys : Array Name := #[]
  let mut seen : Std.HashSet Name := {}
  let mut visited : Std.HashSet (Expr × Bool) := {}
  let mut todo : Array (Expr × Bool) := #[(e, false)]
  while h : 0 < todo.size do
    let (x, inType) := todo.back
    todo := todo.pop
    if visited.contains (x, inType) then continue
    visited := visited.insert (x, inType)
    match x with
    | .const c _ =>
      if inType then tys := tys.push c
      else unless seen.contains c do
        seen := seen.insert c
        out := out.push c
    | .app .. =>
      let fn := x.getAppFn
      let args := x.getAppArgs
      let isProofApp := match fn with
        | .const c ls => (env.find? c matches some (.thmInfo _)) ||
            ((c == ``Eq.mp || c == ``Eq.mpr || c == ``cast) && ls == [Level.zero])
        | _ => false
      if isProofApp then continue
      let fnType? : Option Expr := match fn with
        | .const c _ => (env.find? c).map (·.type)
        | _ => none
      todo := todo.push (fn, inType)
      let mut t? := fnType?
      for a in args do
        let isTy := match t? with
          | some (.forallE _ d _ _) =>
            -- a type (`Sort u`, `Type u`, type formers), but not a proposition (`Prop`): the decided
            -- proposition is evaluated through its instance
            let isTypeSort (s : Expr) : Bool := match s with
              | .sort l => !l.isZero
              | _ => false
            isTypeSort d || isTypeSort d.getForallBody
          | _ => false
        t? := match t? with
          | some (.forallE _ _ b _) => some b
          | _ => none
        todo := todo.push (a, inType || isTy)
    | .lam _ t b _ => todo := (todo.push (t, true)).push (b, inType)
    | .forallE _ t b _ => todo := (todo.push (t, true)).push (b, true)
    | .letE _ t v b _ => todo := ((todo.push (t, true)).push (v, inType)).push (b, inType)
    | .mdata _ b | .proj _ _ b => todo := todo.push (b, inType)
    | _ => pure ()
  return (out, tys)

/-- Constants that must not be staged: those reached from types (the declared types of the definitions
on the way, binder types, type arguments), closed under definition bodies. Replacing such a constant
makes congruence motives ill-typed (e.g. the modulus `p` of `ZMod p`). -/
def typeLevelConsts (env : Environment) (seeds : Array Name) (limit : Nat := 20000) : NameSet := Id.run do
  let mut out : NameSet := {}
  let mut todo := seeds
  let mut n := 0
  while h : 0 < todo.size do
    let c := todo.back
    todo := todo.pop
    if out.contains c then continue
    out := out.insert c
    n := n + 1
    if n > limit then break
    if let some (.defnInfo d) := env.find? c then
      for dep in d.value.getUsedConstants do
        unless out.contains dep do todo := todo.push dep
  return out

/-- Nullary data constants reachable from `e` (through definition bodies, outside proofs and types)
whose bodies compute something, in dependency order: a constant comes after the constants its body
reaches. -/
def stageConstCandidates (e : Expr) (limit : Nat) (visitLimit : Nat := 20000) : MetaM (Array Name) := do
  let env ← getEnv
  let user := kernelReplaceExt.getState env
  let mut order : Array Name := #[]
  let mut seen : NameSet := {}
  let (roots, rootTys) := valueConsts env e
  let mut stack : Array (Name × Bool) := roots.reverse.map (·, false)
  let mut visited := 0
  let mut tySeeds : Array Name := rootTys
  while h : 0 < stack.size do
    let (c, post) := stack.back
    stack := stack.pop
    if post then
      order := order.push c
      continue
    if seen.contains c then continue
    seen := seen.insert c
    visited := visited + 1
    if visited > visitLimit then break
    if kernelPrimitives.contains c || nonEvaluated.contains c || user.contains c then continue
    if let some (.defnInfo d) := env.find? c then
      stack := stack.push (c, true)
      tySeeds := tySeeds ++ d.type.getUsedConstants
      let (deps, tys) := valueConsts env d.value
      tySeeds := tySeeds ++ tys
      for dep in deps do
        unless seen.contains dep do stack := stack.push (dep, false)
  let banned := typeLevelConsts env tySeeds
  let mut out : Array Name := #[]
  let mut typeOk : Std.HashMap Expr Bool := {}
  for c in order do
    if out.size ≥ limit then break
    if banned.contains c then continue
    if c.components.any (fun x => x.toString.startsWith "_auto") then continue
    let some (.defnInfo d) := env.find? c | continue
    unless d.levelParams.isEmpty && d.safety == .safe do continue
    let ok ← match typeOk[d.type]? with
      | some b => pure b
      | none => do
        let b ← isStageType d.type
        typeOk := typeOk.insert d.type b
        pure b
    if ok && !(← isValueLike d.value) then out := out.push c
  return out

/-- The functions the kernel evaluates on `Nat` literals (`Nat.add`, …): when it compares such an
application with another term, it first reduces the arguments to literals (`whnf`), whatever they are. -/
def kernelNatOps : List Name :=
  [``Nat.succ, ``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.beq, ``Nat.ble,
   ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.pow, ``Nat.log2]

/-- `e` is an application of one of `kernelNatOps`. -/
def isKernelNatOpApp (e : Expr) : Bool :=
  match e.getAppFn with
  | .const c _ => kernelNatOps.contains c
  | _ => false

/-- `whnf` of `x` unfolding only instances and reducible constants, within `hb` thousand heartbeats. -/
def whnfInstBounded (x : Expr) (hb : Nat := 2000) : MetaM (Option Expr) := do
  let h ← IO.getNumHeartbeats
  try
    tryCatchRuntimeEx
      (withTheReader Core.Context (fun c => { c with initHeartbeats := h, maxHeartbeats := hb * 1000 })
        (some <$> withTransparency .instances (whnf x)))
      (fun _ => pure none)
  catch _ => pure none

/-- Whether the kernel compares the closed term `s` with an auxiliary constant `a := s` without evaluating
`s`. Below a regular head it unfolds `a` alone and meets `s`. Below an `abbrev` head (projections such as
`HMul.hMul`) it unfolds both at once, `s` one step ahead: harmless when that reaches a regular head through
the projections of instances (`n • P` → the instance's function, which waits for `a`), not when it reaches
one of `kernelNatOps` (`a * b` on `Nat` → `Nat.mul`, whose arguments the kernel reduces to literals first),
a recursor (iota reduction evaluates the major premise) or the projection of a computed structure. -/
partial def auxBridgeSafe (s : Expr) (fuel : Nat := 12) : MetaM Bool := do
  if isKernelNatOpApp s then return false
  let .const c us := s.getAppFn | return false
  let env ← getEnv
  let some (.defnInfo d) := env.find? c | return false
  unless d.hints matches .abbrev do return true
  if fuel == 0 then return false
  let mut t := (d.value.instantiateLevelParams d.levelParams us).beta s.getAppArgs
  for _ in [0:8] do
    let .proj _ i x := t.getAppFn | break
    let some x' ← whnfInstBounded x | return false
    let .const k _ := x'.getAppFn | return false
    let some (.ctorInfo ci) := env.find? k | return false
    let some f := x'.getAppArgs[ci.numParams + i]? | return false
    t := (mkAppN f t.getAppArgs).headBeta
  auxBridgeSafe t (fuel - 1)

/-- The maximal closed subterms of `e` worth staging (not under binders): applications of defined
functions, of a stageable type, not values; innermost first. `e` itself is not included. With `safeOnly`,
only those that the kernel can compare with an auxiliary constant for them without evaluating them
(`auxBridgeSafe`): for the decided term, whose bridge is checked without a heartbeat bound. Inside a
decomposition (bridges bounded by `stageHeartbeats`) a cheap `Nat` operation is worth staging: its value can
make a `match` reducible (e.g. a discriminant `n / 2`). -/
partial def stageSubtermCandidates (e : Expr) (limit : Nat) (safeOnly : Bool := false) :
    MetaM (Array Expr) := do
  let env ← getEnv
  let out ← IO.mkRef (#[] : Array Expr)
  let seen ← IO.mkRef ({} : Std.HashSet Expr)
  let rec go (s : Expr) (top : Bool) : MetaM Unit := do
    if (← out.get).size ≥ limit then return
    if (← seen.get).contains s then return
    seen.modify (·.insert s)
    if s.hasLooseBVars then return
    match s with
    | .mdata _ b => go b top
    | .app .. =>
      let .const fc _ := s.getAppFn | return
      -- the arguments of a proof are never evaluated
      if env.find? fc matches some (.thmInfo _) then return
      for a in s.getAppArgs do go a false
      if top then return
      match env.find? fc with
      | some (.defnInfo _) => pure ()
      | _ => return
      if ← isValueLike s then return
      if safeOnly then
        unless ← auxBridgeSafe s do return
      let T ← try inferType s catch _ => return
      if ← isStageType T then out.modify (·.push s)
    | _ => return
  go e true
  out.get

/-- `[x₁, …, xₙ]` (a chain of `List.cons` ending in `List.nil`): `(u, α, xs)`. -/
partial def listLitElems? (l : Expr) : Option (Level × Expr × Array Expr) :=
  go l #[]
where
  go (l : Expr) (acc : Array Expr) : Option (Level × Expr × Array Expr) :=
    match l.getAppFn, l.getAppArgs with
    | .const ``List.cons [_], #[_, x, t] => go t (acc.push x)
    | .const ``List.nil [u], #[α] => some (u, α, acc)
    | _, _ => none

def mkListLitS (α : Expr) (u : Level) (xs : Array Expr) : Expr :=
  xs.foldr (fun x t => mkApp3 (mkConst ``List.cons [u]) α x t) (mkApp (mkConst ``List.nil [u]) α)

/-- `l₁ ++ (l₂ ++ (… ++ lₖ))` for lists of type `List α`. -/
def mkAppendChain (u : Level) (α : Expr) (ls : Array Expr) : Expr :=
  let LT := mkApp (mkConst ``List [u]) α
  let app (a b : Expr) := mkApp6 (mkConst ``HAppend.hAppend [u, u, u]) LT LT LT
    (mkApp2 (mkConst ``instHAppendOfAppend [u]) LT (mkApp (mkConst ``List.instAppend [u]) α)) a b
  if ls.isEmpty then mkApp (mkConst ``List.nil [u]) α
  else (ls.pop).foldr app ls.back!

/-- Name prefix of staged declarations: `<decl>._ktv` inside an asynchronous branch, otherwise
`_ktv.<module>`. -/
def stagePrefix : CoreM Name := do
  let env ← getEnv
  match env.asyncPrefix? with
  | some p => return p ++ `_ktv
  | none => return `_ktv ++ env.mainModule

/-- State of one staged check. -/
structure StageEnv where
  cfg : KernelConfig
  /-- statement ↦ theorem, for the proofs inside values (`stageProofs`) -/
  pfCache : IO.Ref (Std.HashMap Expr Name)
  counter : IO.Ref Nat
  base : Name
  /-- staged equations left -/
  left : IO.Ref Nat
  /-- kernel time of the staged equations (ms) -/
  ms : IO.Ref Nat
  /-- auxiliary constant ↦ the term compiled code evaluates for it (the subterm it stands for, without
  auxiliary constants) -/
  src : IO.Ref (NameMap Expr)
  /-- constant ↦ (its staged value constant, the theorem `c = value`) -/
  staged : IO.Ref (NameMap (Name × Name))

def StageEnv.fresh (se : StageEnv) (tag : Name) : MetaM Name := do
  let i ← se.counter.modifyGet fun i => (i, i + 1)
  return se.base ++ tag.appendIndexAfter i

def StageEnv.note (se : StageEnv) (msg : String) : MetaM Unit := do
  if se.cfg.trace then eprintRaw s!"NT stage {msg}"

/-- The proofs `of_decide_eq_true inst (Eq.refl true)` inside `e` (as `reifyValue` builds them). -/
partial def collectDecideProofs (e : Expr) : Array Expr :=
  let rec go (x : Expr) : StateT (Std.HashSet Expr × Array Expr) Id Unit := do
    if (← get).1.contains x then return
    modify fun (v, o) => (v.insert x, o)
    if x.isAppOfArity ``of_decide_eq_true 3 then
      modify fun (v, o) => (v, o.push x)
      return
    match x with
    | .app f a => do go f; go a
    | .lam _ t b _ | .forallE _ t b _ => do go t; go b
    | .letE _ t val b _ => do go t; go val; go b
    | .mdata _ b | .proj _ _ b => go b
    | _ => pure ()
  ((go e).run ({}, #[])).run.2.2

/-- Proofs inside a reified value (`of_decide_eq_true inst (Eq.refl true) : p`) become theorems of their
own, one per statement: each is decided by the kernel once, in its own declaration, however many
values contain it. -/
def StageEnv.stageProofs (se : StageEnv) (v : Expr) : MetaM Expr := do
  let pfs := collectDecideProofs v
  if pfs.isEmpty then return v
  let mut names : Std.HashMap Expr Name := {}
  for pf in pfs do
    let p := pf.getArg! 0
    let n ← match (← se.pfCache.get)[p]? with
      | some n => pure n
      | none =>
        let n ← se.fresh `pf
        match ← tryAddTheorem n [] p pf { se.cfg with maxHeartbeats := se.cfg.stageHeartbeats } with
        | .ok _ => pure ()
        | .error ex => throwError m!"a proof inside a staged value was rejected: {ex.toMessageData}"
        se.pfCache.modify (·.insert p n)
        pure n
    names := names.insert pf n
  return v.replace fun x =>
    if x.isAppOfArity ``of_decide_eq_true 3 then (names[x]?).map mkConst else none

/-- A definition `name : T := value` (no universe parameters), checked by the kernel. -/
def addStageDefn (name : Name) (T value : Expr) (hints : ReducibilityHints := .regular 0) : MetaM Bool := do
  if (← getEnv).contains name then return true
  try
    addDeclSync (.defnDecl { name, levelParams := [], type := T, value, hints, safety := .safe, all := [name] })
    return true
  catch _ => return false

/-- The value of the constant `c : T` as a staged value constant (compiled evaluation of `c`, or of the
term registered for it in `src`), or why there is none. -/
def StageEnv.valueConst (se : StageEnv) (c : Name) (T : Expr) : MetaM (Except String Name) := do
  let src := ((← se.src.get).find? c).getD (mkConst c)
  let v ← match ← reifyValue src T with
    | .ok v => pure v
    | .error m => return .error s!"no value: {m.take 200}"
  if sizeUpTo se.cfg.stageSize v ≥ se.cfg.stageSize then return .error "value too large"
  let v ← try se.stageProofs v catch ex => return .error s!"{(← ex.toMessageData.toString).take 200}"
  let vName := `_ktval ++ (← se.fresh `v)
  unless ← addStageDefn vName T v .abbrev do return .error "value rejected by the kernel"
  return .ok vName

/-- Register `c ↦ vName` (proved by `eqName : c = vName`). -/
def StageEnv.register (se : StageEnv) (c vName eqName : Name) : MetaM Unit := do
  let kind := if se.cfg.stageGlobal then AttributeKind.global else AttributeKind.local
  kernelReplaceExt.add (c, vName, eqName) kind
  se.staged.modify (·.insert c (vName, eqName))

/-- The copy of `c` over the replacements registered so far: `(c', proof of c = c')`. -/
def StageEnv.copyOf (se : StageEnv) (c : Name) (T : Expr) : MetaM (Expr × Expr) := do
  let cfg := se.cfg
  let ccfg : CopyConfig := { wf := cfg.wf, wfAcc := cfg.wfAcc, trace := cfg.trace, skipUnchanged := cfg.skipUnchanged, transport := cfg.transport, fastLitMin := cfg.fastLitMin, keepTypes := cfg.keepTypes, csimp := cfg.csimp }
  let r ← kernelCopy (mkConst c) ccfg
  let u ← getLevel T
  match r.replaced.find? (·.1 == c) with
  | some (_, c', h) => return (mkConst c', mkConst h)
  | none => return (mkConst c, mkApp2 (mkConst ``Eq.refl [u]) T (mkConst c))

/-- Prove `c = vName` from `hc : c = x` and `x = vName` by kernel evaluation of `x` within `hb` thousand
heartbeats; register `c ↦ vName` on success. -/
def StageEnv.prove (se : StageEnv) (c vName : Name) (T x hc : Expr) (hb : Nat) (what : String) :
    MetaM Bool := do
  let n ← se.left.get
  if n == 0 then return false
  se.left.set (n - 1)
  let u ← getLevel T
  let vc := mkConst vName
  let pf := mkApp6 (mkConst ``Eq.trans [u]) T (mkConst c) x vc hc (mkApp2 (mkConst ``Eq.refl [u]) T vc)
  let eqName ← se.fresh `eq
  let ty := mkApp3 (mkConst ``Eq [u]) T (mkConst c) vc
  let t0 ← IO.monoMsNow
  match ← tryAddTheorem eqName [] ty pf { se.cfg with maxHeartbeats := hb } with
  | .ok ms =>
    se.ms.modify (· + ms)
    se.register c vName eqName
    se.note s!"{c} {what} ms={ms}"
    return true
  | .error ex =>
    let m := (← ex.toMessageData.toString).replace "\n" " "
    se.note s!"{c} {what}-failed hb={hb} ms={(← IO.monoMsNow) - t0} copy={x != mkConst c} {m.take 120}"
    return false

/-- An auxiliary constant `aux := body` standing for `orig` (a closed term without auxiliary
constants, evaluated by compiled code for its value). -/
def StageEnv.mkAux (se : StageEnv) (body orig : Expr) : MetaM (Option Name) := do
  let T ← inferType orig
  let aux ← se.fresh `t
  -- `abbrev`: unfolded first when the kernel compares it with the term it stands for (a bridge), so
  -- that it never evaluates that term instead
  unless ← addStageDefn aux T body .abbrev do return none
  se.src.modify (·.insert aux orig)
  return some aux

/-- `e` with the auxiliary constants of this staging run unfolded to the subterms they stand for (the
term compiled code evaluates). -/
def StageEnv.unfoldAux (se : StageEnv) (e : Expr) : MetaM Expr := do
  let src ← se.src.get
  return e.replace fun x => match x with
    | .const n _ => src.find? n
    | _ => none

/-- `e` with every `let`/`have` instantiated (long list literals elaborate to `have` chains). -/
partial def zetaAll (e : Expr) : Expr :=
  e.replace fun x => match x with
    | .letE _ _ v b _ => some (zetaAll (b.instantiate1 v))
    | _ => none

/-- `boundedSearch` (below), for the staging steps: a Meta-level step under a heartbeat budget, `none` when
it runs out or throws. -/
def boundedStage {α : Type} (budget : Nat) (x : MetaM (Option α)) : MetaM (Option α) := do
  let x := if budget == 0 then x else do
    let hb ← IO.getNumHeartbeats
    withTheReader Core.Context (fun c => { c with initHeartbeats := hb, maxHeartbeats := budget * 1000 }) x
  tryCatchRuntimeEx x (fun _ => pure none)

/-- Unfold the head of the closed term `b = f a₁ … aₙ` once (unfolding equation of a recursive `f`,
delta otherwise), then reduce matches on constructor-headed values: `(b', proof of b = b')`. -/
def unfoldStep (b : Expr) (budget : Nat) : MetaM (Option (Expr × Expr)) := do
  let .const f us := b.getAppFn | return none
  let env ← getEnv
  let some (.defnInfo d) := env.find? f | return none
  if (← getMatcherInfo? f).isSome then return none
  let args := b.getAppArgs
  let T ← inferType b
  let u ← getLevel T
  -- 1. unfold
  let unfolded? ← boundedStage budget do
    -- the unfolding equation of a recursive `f` (generating it can fail, e.g. for some private
    -- definitions: then delta, as for a non-recursive one)
    match ← (try getUnfoldEqnFor? f catch _ => pure none) with
    | some eqn =>
      let eqT ← inferType (mkConst eqn us)
      let n := eqT.getForallBinderNames.length
      if args.size < n then return none
      let mut h := mkAppN (mkConst eqn us) (args.extract 0 n)
      for a in args.extract n args.size do h ← mkCongrFun h a
      let hT ← inferType h
      let some (_, lhs, rhs) := hT.eq? | return none
      unless lhs == b do return none
      return some (rhs.headBeta, h)
    | none =>
      let v := (d.value.instantiateLevelParams d.levelParams us).beta args
      if v == b then return none
      return some (v, mkApp2 (mkConst ``Eq.refl [u]) T b)
  let some (b₁, pf₁) := unfolded? | return none
  -- 2. matches whose discriminants are constructor-headed
  let mut cur := b₁
  let mut pf := pf₁
  for _ in [0:8] do
    let .const m mus := cur.getAppFn | break
    let some info ← getMatcherInfo? m | break
    let margs := cur.getAppArgs
    let prefixSz := info.numParams + 1 + info.numDiscrs
    if margs.size < prefixSz + info.numAlts then break
    let discrs := margs.extract (info.numParams + 1) prefixSz
    unless ← discrs.allM isCtorHeaded do break
    let pre := mkAppN (mkConst m mus) (margs.extract 0 prefixSz)
    let extra := margs.extract (prefixSz + info.numAlts) margs.size
    -- `∀ alts, pre alts extra = r alts`, checked by the kernel with the alternatives abstracted
    let stmt? ← boundedStage budget do
      let preT ← inferType pre
      forallBoundedTelescope preT info.numAlts fun hs _ => do
        if hs.size != info.numAlts then return none
        let lhs := mkAppN (mkAppN pre hs) extra
        match ← reduceMatcher? lhs with
        | .reduced r =>
          let ty ← mkEq lhs r
          return some (← mkForallFVars hs ty, ← mkLambdaFVars hs (← mkEqRefl lhs))
        | _ => return none
    let some (gty, gpf) := stmt? | break
    let alts := margs.extract prefixSz (prefixSz + info.numAlts)
    let step := mkAppN (mkApp2 (mkConst ``id [Level.zero]) gty gpf) alts
    let stepT ← instantiateForall gty alts
    let some (_, _, r) := stepT.eq? | break
    let r' := r.headBeta
    pf := mkApp6 (mkConst ``Eq.trans [u]) T b cur r pf step
    -- `r = r'` by beta
    pf := mkApp6 (mkConst ``Eq.trans [u]) T b r r' pf (mkApp2 (mkConst ``Eq.refl [u]) T r')
    cur := r'
  if cur == b then return none
  return some (cur, pf)

/-- A projection of a computed structure, `S.f (g a₁ … aₙ)` or `(g a₁ … aₙ).i`: `g` is unfolded (up to 6 times,
zeta-reducing) until the structure is a constructor application, and the projection is reduced:
`(field, proof of b = field)`. The other fields are never evaluated. -/
def projStep (b : Expr) (budget : Nat) : MetaM (Option (Expr × Expr)) := do
  let env ← getEnv
  -- the structure argument and how to rebuild `b` around another structure
  let some (x, rebuild, idx) ← (do
      match b with
      | .proj S i x => pure (some (x, fun y => Expr.proj S i y, i))
      | _ =>
        let .const f _ := b.getAppFn | pure none
        let some info := env.getProjectionFnInfo? f | pure none
        let args := b.getAppArgs
        if h : info.numParams < args.size then
          if args.size != info.numParams + 1 then pure none
          else pure (some (args[info.numParams], fun y => mkAppN b.getAppFn (args.set! info.numParams y), info.i))
        else pure none : MetaM (Option (Expr × (Expr → Expr) × Nat))) | return none
  if x.hasLooseBVars then return none
  let XT ← inferType x
  let T ← inferType b
  let u ← getLevel T
  let ux ← getLevel XT
  let mut cur := x
  let mut pf := mkApp2 (mkConst ``Eq.refl [ux]) XT x
  for _ in [0:6] do
    let z := zetaAll cur
    if z != cur then cur := z
    if let .const c _ := cur.getAppFn then
      if let some (.ctorInfo ci) := env.find? c then
        let some field := cur.getAppArgs[ci.numParams + idx]? | return none
        -- `b = rebuild cur` (congruence) `≡ field` (projection of a constructor)
        let fr ← withLocalDeclD `y XT fun y => mkLambdaFVars #[y] (rebuild y)
        let h := mkApp6 (mkConst ``congrArg [ux, u]) XT T x cur fr pf
        let pf' := mkApp6 (mkConst ``Eq.trans [u]) T b (rebuild cur) field h
          (mkApp2 (mkConst ``Eq.refl [u]) T field)
        return some (field, pf')
    let some (cur', h) ← unfoldStep cur budget | return none
    pf := mkApp6 (mkConst ``Eq.trans [ux]) XT x cur cur' pf h
    cur := cur'
  return none

/-- `Quot.lift f h q` with `q` a computed quotient element: `q` is unfolded (up to 8 times, zeta-reducing)
until it is `Quot.mk r a`, and the lift is reduced to `f a` (`Multiset`/`Finset` operations are lifts of
list functions): `(f a, proof)`. -/
partial def quotStep (b : Expr) (budget : Nat) : MetaM (Option (Expr × Expr)) := do
  unless b.isAppOfArity ``Quot.lift 6 do return none
  let q := b.getArg! 5
  if q.hasLooseBVars then return none
  let QT ← inferType q
  let T ← inferType b
  let u ← getLevel T
  let uq ← getLevel QT
  let mut cur := q
  let mut pf := mkApp2 (mkConst ``Eq.refl [uq]) QT q
  for _ in [0:8] do
    let z := zetaAll cur
    if z != cur then cur := z
    if cur.isAppOfArity ``Quot.mk 3 then
      let a := cur.getArg! 2
      let res := (mkApp (b.getArg! 3) a).headBeta
      let lift (y : Expr) := mkAppN b.getAppFn ((b.getAppArgs).set! 5 y)
      let fr ← withLocalDeclD `y QT fun y => mkLambdaFVars #[y] (lift y)
      let h := mkApp6 (mkConst ``congrArg [uq, u]) QT T q cur fr pf
      -- `Quot.lift f h (Quot.mk r a) ≡ f a` (the kernel's quotient reduction)
      let pf' := mkApp6 (mkConst ``Eq.trans [u]) T b (lift cur) res h (mkApp2 (mkConst ``Eq.refl [u]) T res)
      return some (res, pf')
    -- an inner lift (`Multiset.filter` of `Finset.range`, …) is reduced first
    let step ← match ← quotStep cur budget with
      | some r => pure (some r)
      | none => match ← projStep cur budget with
        | some r => pure (some r)
        | none => unfoldStep cur budget
    let some (cur', h) := step | return none
    pf := mkApp6 (mkConst ``Eq.trans [uq]) QT q cur cur' pf h
    cur := cur'
  return none

/-- The value (a list literal) of `l` if known: a list literal, or a staged constant. -/
def StageEnv.listValue? (se : StageEnv) (l : Expr) : MetaM (Option Expr) := do
  if (listLitElems? l).isSome then return some l
  let .const n _ := l | return none
  let st ← se.staged.get
  let vn := if n.components.contains `_ktval then some n else (st.find? n).map (·.1)
  let some vn := vn | return none
  let some (.defnInfo vd) := (← getEnv).find? vn | return none
  return if (listLitElems? vd.value).isSome then some vd.value else none

/-- The staged equations usable for congruence: constant ↦ (value constant, theorem). -/
def StageEnv.stagedEqs (se : StageEnv) : MetaM (NameMap (Name × Name)) := do
  let mut m := (← se.staged.get)
  for (c, (g, h)) in (kernelReplaceExt.getState (← getEnv)).toList do
    if g.components.contains `_ktval && !m.contains c then m := m.insert c (g, h)
  return m

/-- The term compiled code evaluates for `e`: auxiliary constants unfolded to the subterms they stand
for, value constants replaced by the constants they are the values of (compiled code has neither). -/
def StageEnv.nativeSrc (se : StageEnv) (e : Expr) : MetaM Expr := do
  let src ← se.src.get
  let inv : NameMap Name := (← se.stagedEqs).foldl (fun m c (v, _) => m.insert v c) {}
  let mut e := e
  for _ in [0:16] do
    let e' := e.replace fun x => match x with
      | .const n ls => match src.find? n with
        | some o => some o
        | none => (inv.find? n).map (mkConst · ls)
      | _ => none
    if e' == e then break
    e := e'
  return e

/-- A proof of `e = e'`, `e'` the term `e` with the closed subterms staged as the auxiliary constants
`auxs` replaced by them: one congruence step per constant, in staging order (innermost first). `aᵢ := bᵢ`,
where `bᵢ` is the subterm with the subterms inside it already replaced, and the step rewrites the
occurrences of `bᵢ` from `bᵢ = aᵢ` (`Eq.refl`: the kernel unfolds `aᵢ` and meets the same term). So the
kernel never compares a subterm with a term over other auxiliary constants (it may evaluate the
subterm then, e.g. `Nat.mul` reduces its arguments to literals first), nor `e` with `e'` as a whole (it
may evaluate both, e.g. when the head is a projection such as `Decidable.decide`). `none` if a motive is
not type correct or no constant occurs. -/
def congrSubterms (e T : Expr) (auxs : Array Name) : MetaM (Option (Expr × Expr)) := do
  let env ← getEnv
  let v ← getLevel T
  let mut cur := e
  let mut proof? : Option Expr := none
  for a in auxs do
    let some (.defnInfo d) := env.find? a | return none
    let b := d.value
    unless (cur.find? (· == b)).isSome do continue
    let M? ← try
        withLocalDeclD `y d.type fun y => do
          let M ← mkLambdaFVars #[y] (cur.replace fun x => if x == b then some y else none)
          return if ← isTypeCorrect M then some M else none
      catch _ => pure none
    let some M := M? | return none
    let ui ← getLevel d.type
    let next := cur.replace fun x => if x == b then some (mkConst a) else none
    let step := mkApp6 (mkConst ``congrArg [ui, v]) d.type T b (mkConst a) M
      (mkApp2 (mkConst ``Eq.refl [ui]) d.type b)
    proof? := some <| match proof? with
      | none => step
      | some p => mkApp6 (mkConst ``Eq.trans [v]) T e cur next p step
    cur := next
  return proof?.map (·, cur)

/-- `thm`, an equation `∀ xs, l xs = r xs`, instantiated so that its left side is `lhs` (by unification at
reducible transparency): `(proof of lhs = rhs, rhs)`. -/
def instEqThm (thm : Name) (lhs : Expr) : MetaM (Option (Expr × Expr)) := do
  try
    let c ← mkConstWithFreshMVarLevels thm
    let (xs, _, ty) ← forallMetaTelescopeReducing (← inferType c)
    let some (_, l, r) := ty.eq? | return none
    unless ← withReducible (isDefEq l lhs) do return none
    let pf ← instantiateMVars (mkAppN c xs)
    let r ← instantiateMVars r
    if pf.hasMVar || r.hasMVar then return none
    return some (pf, r)
  catch _ => return none

mutual

/-- Stage the constant `c` (a data constant, or an auxiliary constant for a closed subterm): prove
`c = c_v` for its value, directly if it fits in `stageHeartbeats`, otherwise after staging its parts
(see the section comment); register `c ↦ c_v`. -/
partial def StageEnv.stage (se : StageEnv) (c : Name) (depth : Nat) : MetaM Bool := do
  if (← se.staged.get).contains c then return true
  if (← se.left.get) == 0 then return false
  let some (.defnInfo d) := (← getEnv).find? c | return false
  let T := d.type
  let vName ← match ← se.valueConst c T with
    | .ok v => pure v
    | .error m => se.note s!"{c} no-value {m}"; return false
  let nativeMs ← lastReifyEvalMs.get
  let hb := se.cfg.stageHeartbeats
  let (x, hc) ← se.copyOf c T
  -- an expensive compiled evaluation (a hint of the kernel's cost): decompose first
  if depth > 0 && nativeMs ≥ se.cfg.stageNativeMs then
    se.note s!"{c} native_ms={nativeMs}: decomposing first"
    if ← se.decompose c d.value T depth then return true
    return ← se.prove c vName T x hc hb "direct"
  -- otherwise a small budget first while the term can still be decomposed
  let small := if depth > 0 then max 1 (hb / 4) else hb
  if ← se.prove c vName T x hc small "direct" then return true
  if depth > 0 then
    if ← se.decompose c d.value T depth then return true
  if small < hb then
    if ← se.prove c vName T x hc hb "direct" then return true
  return false

/-- The fold `bv = List.foldl f b l` (`l`'s value: the elements `xs`) over chunks `c₀ ++ (c₁ ++ …)`: the
chunk folds `aux_j := List.foldl f acc_j c_j` are staged in order (`acc₀ = b`, `acc_{j+1}` the value of
`aux_j`), and `c = value` is assembled from `List.foldl_append`. `none` if it does not apply. -/
partial def StageEnv.foldlChunks (se : StageEnv) (c : Name) (bv T : Expr) (u : Level) (pfv f b : Expr)
    (lu : Level) (γ : Expr) (xs : Array Expr) (depth : Nat) : MetaM (Option Bool) := do
  let k := min 32 (xs.size / 2)
  let chunks := (List.range k).toArray.map fun j =>
    mkListLitS γ lu (xs.extract (j * xs.size / k) ((j + 1) * xs.size / k))
  let us := bv.getAppFn.constLevels!
  let α := bv.getArg! 0
  let foldlE (acc l : Expr) := mkAppN (mkConst ``List.foldl us) #[α, γ, f, acc, l]
  -- `bv = foldl f b (c₀ ++ (c₁ ++ …))`: the list by unfolding, under a congruence
  let chain := mkAppendChain lu γ chunks
  let LT := mkApp (mkConst ``List [lu]) γ
  let l := bv.getArg! 4
  let fl ← withLocalDeclD `y LT fun y => mkLambdaFVars #[y] (foldlE b y)
  let hl := mkApp2 (mkConst ``Eq.refl [lu.succ]) LT l
  let mut pf := mkApp6 (mkConst ``Eq.trans [u]) T (mkConst c) bv (foldlE b chain) pfv
    (mkApp6 (mkConst ``congrArg [lu.succ, u]) LT T l chain fl hl)
  let mut cur := foldlE b chain
  let mut acc := b
  for j in [0:k] do
    let rest := mkAppendChain lu γ (chunks.extract (j + 1) k)
    let piece := foldlE acc chunks[j]!
    let some aux ← se.mkAux piece (← se.nativeSrc piece) | return none
    unless ← se.stage aux (depth - 1) do return some false
    let some (va, ha) := (← se.staged.get).find? aux | return some false
    -- `piece = va`
    let hpiece := mkApp6 (mkConst ``Eq.trans [u]) T piece (mkConst aux) (mkConst va)
      (mkApp2 (mkConst ``Eq.refl [u]) T piece) (mkConst ha)
    if j + 1 < k then
      -- `foldl f acc (c_j ++ rest) = foldl f (foldl f acc c_j) rest = foldl f va rest`
      let some (happ, rhs) ← instEqThm ``List.foldl_append cur | return none
      let fr ← withLocalDeclD `y T fun y => mkLambdaFVars #[y] (foldlE y rest)
      let next := foldlE (mkConst va) rest
      let hcongr := mkApp6 (mkConst ``congrArg [u, u]) T T piece (mkConst va) fr hpiece
      pf := mkApp6 (mkConst ``Eq.trans [u]) T (mkConst c) cur rhs pf happ
      pf := mkApp6 (mkConst ``Eq.trans [u]) T (mkConst c) rhs next pf hcongr
      cur := next
      acc := mkConst va
    else
      pf := mkApp6 (mkConst ``Eq.trans [u]) T (mkConst c) cur (mkConst va) pf hpiece
      let n ← se.left.get
      if n == 0 then return some false
      se.left.set (n - 1)
      let eqName ← se.fresh `eq
      let ty := mkApp3 (mkConst ``Eq [u]) T (mkConst c) (mkConst va)
      match ← tryAddTheorem eqName [] ty pf { se.cfg with maxHeartbeats := se.cfg.stageHeartbeats } with
      | .ok ms =>
        se.register c va eqName
        se.note s!"{c} foldl {xs.size} in {k} chunks bridge ms={ms}"
        return some true
      | .error ex =>
        se.note s!"{c} foldl bridge-failed {((← ex.toMessageData.toString).replace "\n" " ").take 160}"
        return some false
  return some false

/-- The fold `bv = List.foldr f b l` (`l`'s value: the elements `xs`) over chunks `c₀ ++ (c₁ ++ …)`: the
chunk folds `aux_j := List.foldr f acc_j c_j` are staged from the last chunk to the first (`acc_{k-1} = b`,
`acc_j` the value of `aux_{j+1}`), and `c = value` is assembled from `List.foldr_append`. `none` if it does
not apply. -/
partial def StageEnv.foldrChunks (se : StageEnv) (c : Name) (bv T : Expr) (u : Level) (pfv f b : Expr)
    (lu : Level) (γ : Expr) (xs : Array Expr) (depth : Nat) : MetaM (Option Bool) := do
  let k := min 32 (xs.size / 2)
  let chunks := (List.range k).toArray.map fun j =>
    mkListLitS γ lu (xs.extract (j * xs.size / k) ((j + 1) * xs.size / k))
  let us := bv.getAppFn.constLevels!
  let β := bv.getArg! 1
  let foldrE (acc l : Expr) := mkAppN (mkConst ``List.foldr us) #[γ, β, f, acc, l]
  let LT := mkApp (mkConst ``List [lu]) γ
  let rest (j : Nat) := mkAppendChain lu γ (chunks.extract j k)
  -- stage from the last chunk: `h : foldr f b (rest j) = v_j`
  let mut h? : Option Expr := none
  let mut acc := b
  for jj in [0:k] do
    let j := k - 1 - jj
    let piece := foldrE acc chunks[j]!
    let some aux ← se.mkAux piece (← se.nativeSrc piece) | return none
    unless ← se.stage aux (depth - 1) do return some false
    let some (va, ha) := (← se.staged.get).find? aux | return some false
    let hpiece := mkApp6 (mkConst ``Eq.trans [u]) T piece (mkConst aux) (mkConst va)
      (mkApp2 (mkConst ``Eq.refl [u]) T piece) (mkConst ha)
    match h? with
    | none => h? := some hpiece  -- `rest (k-1) = c_{k-1}`
    | some hnext =>
      -- `foldr f b (c_j ++ rest (j+1)) = foldr f (foldr f b (rest (j+1))) c_j = foldr f v_{j+1} c_j = v_j`
      let cur := foldrE b (rest j)
      let some (happ, rhs) ← instEqThm ``List.foldr_append cur | return none
      let fr ← withLocalDeclD `y T fun y => mkLambdaFVars #[y] (foldrE y chunks[j]!)
      let hcongr := mkApp6 (mkConst ``congrArg [u, u]) T T (foldrE b (rest (j + 1))) acc fr hnext
      let h1 := mkApp6 (mkConst ``Eq.trans [u]) T cur rhs piece happ hcongr
      h? := some (mkApp6 (mkConst ``Eq.trans [u]) T cur piece (mkConst va) h1 hpiece)
    acc := mkConst va
  let some h := h? | return some false
  -- `c = bv = foldr f b (c₀ ++ …) = value`
  let chain := rest 0
  let l := bv.getArg! 4
  let fl ← withLocalDeclD `y LT fun y => mkLambdaFVars #[y] (foldrE b y)
  let hl := mkApp2 (mkConst ``Eq.refl [lu.succ]) LT l
  let pf := mkApp6 (mkConst ``Eq.trans [u]) T (mkConst c) bv (foldrE b chain) pfv
    (mkApp6 (mkConst ``congrArg [lu.succ, u]) LT T l chain fl hl)
  let pf := mkApp6 (mkConst ``Eq.trans [u]) T (mkConst c) (foldrE b chain) acc pf h
  let n ← se.left.get
  if n == 0 then return some false
  se.left.set (n - 1)
  let eqName ← se.fresh `eq
  let .const va _ := acc | return some false
  let ty := mkApp3 (mkConst ``Eq [u]) T (mkConst c) acc
  match ← tryAddTheorem eqName [] ty pf { se.cfg with maxHeartbeats := se.cfg.stageHeartbeats } with
  | .ok ms =>
    se.register c va eqName
    se.note s!"{c} foldr {xs.size} in {k} chunks bridge ms={ms}"
    return some true
  | .error ex =>
    se.note s!"{c} foldr bridge-failed {((← ex.toMessageData.toString).replace "\n" " ").take 160}"
    return some false

/-- The filter `bv = List.filter p l` (`l`'s value: the elements `xs`) over chunks: `filter p` distributes
over the chunks (`List.filter_append`), each chunk filter is staged, and the join of the values is staged
(appends of literals). `none` if it does not apply. -/
partial def StageEnv.filterChunks (se : StageEnv) (c : Name) (bv T : Expr) (u : Level) (pfv p : Expr)
    (lu : Level) (γ : Expr) (xs : Array Expr) (depth : Nat) : MetaM (Option Bool) := do
  let k := min 32 (xs.size / 2)
  let chunks := (List.range k).toArray.map fun j =>
    mkListLitS γ lu (xs.extract (j * xs.size / k) ((j + 1) * xs.size / k))
  let us := bv.getAppFn.constLevels!
  let filterE (l : Expr) := mkAppN (mkConst ``List.filter us) #[γ, p, l]
  let LT := mkApp (mkConst ``List [lu]) γ
  let rest (j : Nat) := mkAppendChain lu γ (chunks.extract j k)
  -- `filter p (rest j) = F j`, `F j = filter p c_j ++ F (j+1)`, from the last chunk
  let pieces := chunks.map filterE
  let F (j : Nat) := mkAppendChain lu γ (pieces.extract j k)
  let mut h := mkApp2 (mkConst ``Eq.refl [u]) T (pieces[k - 1]!)
  for jj in [1:k] do
    let j := k - 1 - jj
    let cur := filterE (rest j)
    let some (happ, rhs) ← instEqThm ``List.filter_append cur | return none
    -- `rhs = filter p c_j ++ filter p (rest (j+1))`; then congruence with `h` on the second part
    let fr ← withLocalDeclD `y LT fun y => mkLambdaFVars #[y] (mkAppendChain lu γ #[pieces[j]!, y])
    let hc := mkApp6 (mkConst ``congrArg [u, u]) LT LT (filterE (rest (j + 1))) (F (j + 1)) fr h
    h := mkApp6 (mkConst ``Eq.trans [u]) T cur rhs (F j) happ hc
  -- the chunk filters, staged
  let mut auxs : Array Name := #[]
  for pc in pieces do
    let some aux ← se.mkAux pc (← se.nativeSrc pc) | return none
    unless ← se.stage aux (depth - 1) do return some false
    auxs := auxs.push aux
  -- `F 0 = aux₀ ++ (aux₁ ++ …)` by congruence, the join staged
  let F0 := F 0
  let some (hF, joined) ← congrSubterms F0 T auxs | return some false
  let some a ← se.mkAux joined (← se.nativeSrc joined) | return none
  unless ← se.stage a 0 do return some false
  let some (va, ha) := (← se.staged.get).find? a | return some false
  -- `c = bv = filter p chain = F 0 = joined ≡ a = va`
  let chain := rest 0
  let l := bv.getArg! 2
  let fl ← withLocalDeclD `y LT fun y => mkLambdaFVars #[y] (filterE y)
  let hl := mkApp2 (mkConst ``Eq.refl [lu.succ]) LT l
  let tr (a b c' h₁ h₂ : Expr) := mkApp6 (mkConst ``Eq.trans [u]) T a b c' h₁ h₂
  let pf := tr (mkConst c) bv (filterE chain) pfv (mkApp6 (mkConst ``congrArg [lu.succ, u]) LT T l chain fl hl)
  let pf := tr (mkConst c) (filterE chain) F0 pf h
  let pf := tr (mkConst c) F0 joined pf hF
  let pf := tr (mkConst c) joined (mkConst va) pf
    (tr joined (mkConst a) (mkConst va) (mkApp2 (mkConst ``Eq.refl [u]) T (mkConst a)) (mkConst ha))
  let n ← se.left.get
  if n == 0 then return some false
  se.left.set (n - 1)
  let eqName ← se.fresh `eq
  let ty := mkApp3 (mkConst ``Eq [u]) T (mkConst c) (mkConst va)
  match ← tryAddTheorem eqName [] ty pf { se.cfg with maxHeartbeats := se.cfg.stageHeartbeats } with
  | .ok ms =>
    se.register c va eqName
    se.note s!"{c} filter {xs.size} in {k} chunks bridge ms={ms}"
    return some true
  | .error ex =>
    se.note s!"{c} filter bridge-failed {((← ex.toMessageData.toString).replace "\n" " ").take 160}"
    return some false

/-- Stage the parts of `c`'s body `b`, then `c` over them; `true` on success.
The body is first zeta-reduced (long list literals elaborate to `have` chains) and the staged constants
in it replaced by their values by congruence, `c = b_v`; the pieces are cut from `b_v`, so that
`b_v ≡ a` holds by unfolding for the term `a` assembled from them. -/
partial def StageEnv.decompose (se : StageEnv) (c : Name) (b₀ T : Expr) (depth : Nat) :
    MetaM Bool := do
  let u ← getLevel T
  let b := zetaAll b₀
  -- `c = b_v`: unfolding, then congruence from the staged equations of the constants in `b`
  let eqs ← se.stagedEqs
  let (bv, pfv) ← match ← (try congrSubst b T eqs catch _ => pure none) with
    | some h => pure (substConsts (eqs.foldl (fun m k (v, _) => m.insert k v) {}) b,
        mkApp6 (mkConst ``Eq.trans [u]) T (mkConst c) b
          (substConsts (eqs.foldl (fun m k (v, _) => m.insert k v) {}) b)
          (mkApp2 (mkConst ``Eq.refl [u]) T (mkConst c)) h)
    | none => pure (b, mkApp2 (mkConst ``Eq.refl [u]) T (mkConst c))
  -- `c = a` from `c = b_v` (`pfv`) and `b_v = a` (`h`), then the staged `a = va`
  let finish (a : Name) (bva : Expr) (what : String) : MetaM Bool := do
    let some (va, ha) := (← se.staged.get).find? a | return false
    let n ← se.left.get
    if n == 0 then return false
    se.left.set (n - 1)
    let pfa := mkApp6 (mkConst ``Eq.trans [u]) T bv (mkConst a) (mkConst va) bva (mkConst ha)
    let pf := mkApp6 (mkConst ``Eq.trans [u]) T (mkConst c) bv (mkConst va) pfv pfa
    let eqName ← se.fresh `eq
    let ty := mkApp3 (mkConst ``Eq [u]) T (mkConst c) (mkConst va)
    match ← tryAddTheorem eqName [] ty pf { se.cfg with maxHeartbeats := se.cfg.stageHeartbeats } with
    | .ok ms => se.register c va eqName; se.note s!"{c} {what} bridge ms={ms}"; return true
    | .error ex =>
      se.note s!"{c} {what} bridge-failed {((← ex.toMessageData.toString).replace "\n" " ").take 160}"
      return false
  let reflTo (a : Name) := mkApp2 (mkConst ``Eq.refl [u]) T (mkConst a)
  let chunked (xs : Array Expr) (mk : Array Expr → Expr) (resU : Level) (resT : Expr)
      (what : String) : MetaM Bool := do
    let k := min 32 (xs.size / 2)
    let mut parts := #[]
    for j in [0:k] do
      let ch := xs.extract (j * xs.size / k) ((j + 1) * xs.size / k)
      let piece := mk ch
      let some aux ← se.mkAux piece (← se.nativeSrc piece) | return false
      unless ← se.stage aux (depth - 1) do return false
      parts := parts.push (mkConst aux)
    let whole := mkAppendChain resU resT parts
    let some a ← se.mkAux whole (← se.nativeSrc whole) | return false
    se.note s!"{c} {what} {xs.size} in {k} chunks"
    unless ← se.stage a 0 do return false
    -- `b_v ≡ chunk₁ ++ …` by unfolding: the elements are the same expressions
    finish a (reflTo a) what
  -- a list literal: chunks
  if let some (lu, α, xs) := listLitElems? bv then
    if xs.size ≥ 4 then
      return ← chunked xs (mkListLitS α lu) lu α "list"
  -- `List.map f l` with `l` of known value: chunks of `l`
  if bv.isAppOfArity ``List.map 4 then
    if let some lval ← se.listValue? (bv.getArg! 3) then
      if let some (lu, α, xs) := listLitElems? lval then
        if xs.size ≥ 4 then
          let us := bv.getAppFn.constLevels!
          let β := bv.getArg! 1
          let f := bv.getArg! 2
          let ub := match us with | [_, v] => v | _ => lu
          return ← chunked xs (fun ch => mkAppN (mkConst ``List.map us) #[α, β, f, mkListLitS α lu ch])
            ub β "map"
  -- `List.foldl f b l` with `l` of known value: the fold over chunks of `l`, one after the other
  -- (`List.foldl_append`), each chunk staged with the accumulator value of the chunks before it
  if bv.isAppOfArity ``List.foldl 5 then
    if let some lval ← se.listValue? (bv.getArg! 4) then
      if let some (lu, γ, xs) := listLitElems? lval then
        if xs.size ≥ 4 then
          if let some r ← se.foldlChunks c bv T u pfv (bv.getArg! 2) (bv.getArg! 3) lu γ xs depth then
            return r
  -- `List.foldr f b l` likewise, from the last chunk to the first (`List.foldr_append`)
  if bv.isAppOfArity ``List.foldr 5 then
    if let some lval ← se.listValue? (bv.getArg! 4) then
      if let some (lu, γ, xs) := listLitElems? lval then
        if xs.size ≥ 4 then
          if let some r ← se.foldrChunks c bv T u pfv (bv.getArg! 2) (bv.getArg! 3) lu γ xs depth then
            return r
  -- `List.filter p l` likewise: `filter p (c₀ ++ (c₁ ++ …)) = filter p c₀ ++ (filter p c₁ ++ …)`
  -- (`List.filter_append`), the chunk filters staged, their values appended
  if bv.isAppOfArity ``List.filter 3 then
    if let some lval ← se.listValue? (bv.getArg! 2) then
      if let some (lu, γ, xs) := listLitElems? lval then
        if xs.size ≥ 4 then
          if let some r ← se.filterChunks c bv T u pfv (bv.getArg! 1) lu γ xs depth then
            return r
  -- closed subterms of the body
  let subs ← stageSubtermCandidates bv 64
  let mut subst : Std.HashMap Expr Name := {}
  let mut order : Array Name := #[]
  for s in subs do
    let sub := subst
    let body := s.replace fun x => if x == s then none else (sub[x]?).map mkConst
    let some aux ← se.mkAux body (← se.nativeSrc s) | continue
    if ← se.stage aux (depth - 1) then
      subst := subst.insert s aux
      order := order.push aux
  if !subst.isEmpty then
    let sub := subst
    -- `b_v = b'` by congruence, innermost first (fallback: unfolding)
    let (b', hb?) ← match ← congrSubterms bv T order with
      | some (h, b'') => pure (b'', some h)
      | none => pure (bv.replace fun x => (sub[x]?).map mkConst, none)
    let some a ← se.mkAux b' (← se.nativeSrc bv) | return false
    se.note s!"{c} subterms staged={subst.size}"
    if ← se.stage a (depth - 1) then
      -- `b' ≡ a`
      let bva := match hb? with
        | some h => mkApp6 (mkConst ``Eq.trans [u]) T bv b' (mkConst a) h (reflTo a)
        | none => reflTo a
      return ← finish a bva "subterms"
    return false
  -- a projection of a computed structure: reduce it (the structure is unfolded to a constructor), else
  -- unfold the head
  let step? ← match ← projStep bv se.cfg.searchHeartbeats with
    | some r => pure (some r)
    | none => match ← quotStep bv se.cfg.searchHeartbeats with
      | some r => pure (some r)
      | none => unfoldStep bv se.cfg.searchHeartbeats
  if let some (b', pf) := step? then
    let some a ← se.mkAux b' (← se.nativeSrc b') | return false
    se.note s!"{c} unfolded {bv.getAppFn.constName?.getD .anonymous}"
    if ← se.stage a (depth - 1) then
      -- `b_v = b'` (`pf`) `≡ a`
      return ← finish a (mkApp6 (mkConst ``Eq.trans [u]) T bv b' (mkConst a) pf (reflTo a)) "unfold"
  se.note s!"{c} no decomposition (head {bv.getAppFn.constName?.getD .anonymous})"
  return false

end

/-- Stage the data constants reachable from `e` (step 1 of `proveTrueStaged`): `(candidates, staged)`.
With `stageGlobal`, a module that only does this serves every fact that imports it. -/
def stageConstantsOf (e : Expr) (name : Name) (cfg : KernelConfig) : MetaM (Nat × Nat) := do
  let pre ← stagePrefix
  let se : StageEnv := {
    cfg, pfCache := ← IO.mkRef {}, counter := ← IO.mkRef 0, base := pre ++ name,
    left := ← IO.mkRef cfg.stageMax, ms := ← IO.mkRef 0, src := ← IO.mkRef {}, staged := ← IO.mkRef {} }
  let cands ← stageConstCandidates e cfg.stageMax
  let mut ok := 0
  for c in cands do
    if ← se.stage c cfg.stageDepth then ok := ok + 1
  return (cands.size, ok)

/-- `e = true` by staged evaluation (see the section comment). -/
def proveTrueStaged (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  unless lvls.isEmpty do throwError "NativeTrust: staging needs a statement without universe parameters"
  let t0 ← IO.monoMsNow
  let pre ← stagePrefix
  let se : StageEnv := {
    cfg, pfCache := ← IO.mkRef {}, counter := ← IO.mkRef 0, base := pre ++ name,
    left := ← IO.mkRef cfg.stageMax, ms := ← IO.mkRef 0, src := ← IO.mkRef {}, staged := ← IO.mkRef {} }
  -- 1. data constants reachable from `e`
  let cands ← stageConstCandidates e cfg.stageMax
  let mut ok := 0
  for c in cands do
    if ← se.stage c cfg.stageDepth then ok := ok + 1
  let t1 ← IO.monoMsNow
  if cfg.trace then
    eprintRaw s!"NT {name} stage constants={cands.size} staged={ok} ms={t1 - t0}"
  -- 2. the decided term: its closed subterms, replaced by staged auxiliary constants
  let mut e' := e
  let mut hE? : Option Expr := none
  if cfg.stageSubterms then
    let subs ← stageSubtermCandidates e 64 (safeOnly := true)
    let mut subst : Std.HashMap Expr Name := {}
    let mut order : Array Name := #[]
    for s in subs do
      let sub := subst
      let body := s.replace fun x => if x == s then none else (sub[x]?).map mkConst
      let some aux ← se.mkAux body s | continue
      if ← se.stage aux cfg.stageDepth then
        subst := subst.insert s aux
        order := order.push aux
    -- `e = e'` by congruence, innermost first (fallback: the kernel compares them by unfolding)
    match ← congrSubterms e (mkConst ``Bool) order with
    | some (h, e'') => e' := e''; hE? := some h
    | none => let sub := subst; e' := e.replace fun x => (sub[x]?).map mkConst
    if cfg.trace then
      eprintRaw s!"NT {name} stage subterms={subs.size} staged={subst.size} congr={hE?.isSome} ms={(← IO.monoMsNow) - t1}"
  -- 3. the decided term over the values
  let steps := cfg.stageMax - (← se.left.get)
  if e' == e then
    return { (← proveTrueByKernel e name lvls cfg native?) with pieces := steps + 1 }
  let name' := name ++ `staged
  let r ← proveTrueByKernel e' name' lvls cfg native?
  let bridge := match hE? with
    | some h => mkApp6 (mkConst ``Eq.trans [1]) (mkConst ``Bool) e e' boolTrue h (mkConst name')
    | none => mkConst name'
  match ← tryAddTheorem name lvls (mkBoolEq e boolTrue) bridge cfg with
  | .ok _ => pure ()
  | .error ex => throwError m!"NativeTrust: the kernel rejected the staged bridge:{indentD ex.toMessageData}"
  return { r with thm := name, pieces := steps + 1 }

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
  let pname := c.name ++ (`p).appendIndexAfter i
  -- with staging, a piece that does not check within `quickHeartbeats` is staged
  let r ← if c.cfg.stage && c.lvls.isEmpty then do
      let quick := { c.cfg with maxHeartbeats := c.cfg.quickHeartbeats, blockedHeartbeats := 0,
                                diagnoseFalse := false, accFallback := false }
      let r? ← if c.cfg.quickHeartbeats != 0 then
          tryCatchRuntimeEx (some <$> proveTrueByKernelCore e pname c.lvls quick c.native?) fun _ => pure none
        else pure none
      match r? with
      | some r => pure r
      | none => proveTrueStaged e pname c.lvls c.cfg c.native?
    else proveTrueByKernel e pname c.lvls c.cfg c.native?
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
  if budget ≤ 1 && !cfg.witness && !cfg.stage then return ← proveTrueByKernel e name lvls cfg native?
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
  -- staged evaluation of the whole term when no structured check is asked for (with one, the pieces are
  -- staged: `SplitCtx.leaf`)
  if cfg.stage && cfg.shards == 0 && cfg.split ≤ 1 && !cfg.propSplit then
    return ← proveTrueStaged e name lvls cfg native?
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
