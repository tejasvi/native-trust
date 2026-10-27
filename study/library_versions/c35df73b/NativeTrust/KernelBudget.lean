module

public meta import Lean.Elab.Command
public meta import Lean.Meta.InferType
-- `String.splitOn` lives here in module-system files on Lean 4.27-4.29 (present up to the nightly)
public meta import Init.Data.String.Legacy

/-!
# Plain kernel evaluation within a budget: shared by the linter and `NativeTrust.KernelFirst`

The budget option, the verdicts of plain kernel evaluation (what `decide +kernel` does) and a cache of
them, and a static triage for the plain kernel. A `module`, so that `NativeTrust.KernelFirst` (also a
`module`) can be imported from module-system files; it imports only Lean.
-/

public meta section

open Lean

namespace NativeTrust

register_option nativeTrust.kernelHeartbeats : Nat := {
  defValue := 2000
  descr := "NativeTrust: heartbeat budget (in thousands, like `maxHeartbeats`) for the plain kernel \
    evaluation tried by `linter.nativeTrust`, `#native_decide_audit` and \
    `NativeTrust.KernelFirst`; 0 = no limit"
}

/-- The outcome of evaluating `e = true` in the kernel, without any NativeTrust transformation. -/
inductive PlainVerdict where
  /-- The kernel proved it, in `ms` milliseconds. -/
  | proved (ms : Nat)
  /-- Heartbeat budget exhausted. -/
  | budget (ms : Nat)
  /-- Out of other resources (recursion depth, stack); `msg` says which. -/
  | resources (msg : String)
  /-- The kernel finished, but `e` did not reduce to `true` (it is stuck, or `false`). -/
  | notTrue (msg : String)
  deriving Inhabited

/-- Results of plain kernel evaluations already made in this process, keyed by the decided term, the
heartbeat budget and `maxRecDepth`: a fact repeated by `all_goals` is evaluated once, and the linter
does not evaluate again what `NativeTrust.KernelFirst` tried. -/
initialize plainAttempts : IO.Ref (Std.HashMap (Expr × Nat × Nat) PlainVerdict) ← IO.mkRef {}

/-- First line of a message, at most `n` characters. -/
def firstLine (s : String) (n : Nat := 300) : String :=
  let l := (s.splitOn "\n").headD ""
  if l.length > n then s!"{l.take n}…" else l

/-- Classify a failed kernel check. -/
def classifyKernelFailure (ex : Exception) (ms : Nat) : CoreM PlainVerdict := do
  let msg ← ex.toMessageData.toString
  if (msg.splitOn "deterministic timeout").length > 1 || (msg.splitOn "heartbeats").length > 1 then
    return .budget ms
  if (msg.splitOn "deep recursion").length > 1 || (msg.splitOn "maximum recursion depth").length > 1
      || (msg.splitOn "stack overflow").length > 1 then
    return .resources (firstLine msg)
  return .notTrue (firstLine msg)

/-- The tactic that made native axiom `ax` (`native_decide`, `decide` for `decide +native`,
`bv_decide`). -/
def nativeTacticOf (ax : Name) : Name :=
  ((privateToUserName ax).components.dropWhile (· != `_native)).drop 1 |>.headD .anonymous

/-- How a user writes the tactic that made a native axiom. -/
def nativeTacticDisplay (tac : Name) : String :=
  if tac == `decide then "decide +native" else tac.toString

/-- Is `c` a constant that the kernel cannot unfold (the conditions of NativeTrust's
`blockerReason`, except well-founded recursion)? Axioms whose type is a proposition are proofs, which
evaluation never reduces; in a module-system file, imported theorems look like such axioms. -/
def isPlainBlocker (env : Environment) (c : Name) : CoreM Bool := do
  if c == `WellFounded.extrinsicFix || c == `WellFounded.extrinsicFix₂ ||
      c == `WellFounded.extrinsicFix₃ || c == `Lean.Order.fix || c == ``Lean.Loop.forIn then
    return true
  match env.find? c with
  | some (.opaqueInfo _) => return true
  | some (.axiomInfo a) =>
    if c == ``propext || c == ``Quot.sound || c.components.contains `_native then return false
    return !(← (Meta.isProp a.type).run')
  | some (.defnInfo d) => return d.safety != .safe
  | _ => return false

/-- Panic and trace messages: the kernel never evaluates them. -/
def plainNonEvaluated : List Name :=
  [``mkPanicMessage, ``mkPanicMessageWithDecl, ``dbgTrace, ``dbgTraceIfShared]

/-- `Nat` operations that the kernel computes on literals itself (GMP), whatever their definitions;
in a module-system file their definitions are not visible, which does not matter. -/
def kernelNatPrimitives : List Name :=
  [``Nat.add, ``Nat.sub, ``Nat.mul, ``Nat.div, ``Nat.mod, ``Nat.gcd, ``Nat.beq, ``Nat.ble,
   ``Nat.land, ``Nat.lor, ``Nat.xor, ``Nat.shiftLeft, ``Nat.shiftRight, ``Nat.pow, ``Nat.log2]

/-- Constants that the kernel cannot unfold, reachable from `e` through definition bodies as plain
kernel evaluation sees them (no copies, no replacements), at most `limit`. `WellFounded.fix` is not
counted (it is often reachable only on branches that the evaluation never takes), nor are panic and
trace messages and the `Nat` operations that the kernel computes itself. -/
def plainBlockers (e : Expr) (limit : Nat := 3) : CoreM (Array Name) := do
  let env ← getEnv
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  let mut out : Array Name := #[]
  for c in e.getUsedConstants do
    unless seen.contains c do
      seen := seen.insert c
      queue := queue.push c
  let mut i := 0
  while h : i < queue.size do
    let c := queue[i]
    i := i + 1
    if c == ``WellFounded.fix || plainNonEvaluated.contains c || kernelNatPrimitives.contains c then
      continue
    if ← isPlainBlocker env c then
      out := out.push c
      if out.size ≥ limit then break
      continue
    if let some (.defnInfo d) := env.find? c then
      for dep in d.value.getUsedConstants do
        unless seen.contains dep do
          seen := seen.insert dep
          queue := queue.push dep
  return out

/-- The path of definitions from `e` to `WellFounded.fix`, if it is reachable. -/
def wfPath? (e : Expr) : CoreM (Option (List Name)) := do
  let env ← getEnv
  let mut parent : Std.HashMap Name Name := {}
  let mut seen : Std.HashSet Name := {}
  let mut queue : Array Name := #[]
  for c in e.getUsedConstants do
    unless seen.contains c do
      seen := seen.insert c
      queue := queue.push c
  let mut i := 0
  while h : i < queue.size do
    let c := queue[i]
    i := i + 1
    if c == ``WellFounded.fix then
      let mut path := [c]
      let mut cur := c
      for _ in [0:1000] do
        match parent[cur]? with
        | some p => path := p :: path; cur := p
        | none => break
      return some path
    if plainNonEvaluated.contains c then continue
    if let some (.defnInfo d) := env.find? c then
      for dep in d.value.getUsedConstants do
        unless seen.contains dep do
          seen := seen.insert dep
          parent := parent.insert dep c
          queue := queue.push dep
  return none

/-- `plainBlockers`, cached per term. -/
initialize plainBlockersCache : IO.Ref (Std.HashMap Expr (Array Name)) ← IO.mkRef {}

def cachedPlainBlockers (e : Expr) : CoreM (Array Name) := do
  if let some bs := (← plainBlockersCache.get)[e]? then return bs
  let bs ← plainBlockers e
  plainBlockersCache.modify (·.insert e bs)
  return bs

end NativeTrust
