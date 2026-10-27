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

/-- Constants reachable from `e` through definition bodies that the kernel cannot unfold. With
`static`, `e` is the original term (no `kernelCopy`): well-founded recursion and registered
replacements are followed as the copies would have them, so no copy needs to be built. -/
def findBlockers (e : Expr) (static : Bool := false) : CoreM (Array Blocker) := do
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
      for dep in d.value.getUsedConstants do
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
  let blockers ← findBlockers e'
  if blockers.isEmpty then
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
  let r ← kernelCopy e { opt := cfg.opt, wf := cfg.wf, wfAcc := cfg.wfAcc, trace := cfg.trace }
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

/-- `proveTrueByKernelCore` with the fuel route, and the accessibility-generator route as a
fallback when well-founded recursion is what stops the fuel route (`KernelConfig.accFallback`). -/
def proveTrueByKernel (e : Expr) (name : Name) (lvls : List Name) (cfg : KernelConfig)
    (native? : Option Bool := none) : MetaM KernelResult := do
  try proveTrueByKernelCore e name lvls cfg native?
  catch ex =>
    unless cfg.wf && !cfg.wfAcc && cfg.accFallback do throw ex
    -- only when well-founded recursion is reachable at all
    unless (← findBlockers e).any (·.name == ``WellFounded.fix) do throw ex
    if cfg.trace then eprintRaw s!"NT {name} acc-fallback"
    try proveTrueByKernelCore e name lvls { cfg with wfAcc := true } native?
    catch _ => throw ex

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
