import Lean
import NativeTrust.Kernel

/-!
# The `kdecide` tactic

`kdecide` proves a closed decidable proposition `p` like `native_decide`, but the proof is
checked by Lean's kernel and depends only on `propext`, `Classical.choice` and `Quot.sound`:

1. compiled evaluation of `decide p` (an untrusted oracle) fails fast on false propositions;
2. definitions reachable from the decision procedure are made kernel-reducible (`kernelCopy`);
3. the kernel evaluates `decide p` to `true` (`proveTrueByKernel`);
4. the axioms of the result are checked.

If the kernel cannot finish, the error says why: the proposition is false in the logic,
evaluation is blocked by a constant without a kernel definition (with the path to it), or the
kernel ran out of resources.

Options (`kdecide (config := { ... })`, or `kdecide +opt`, `kdecide (split := 8)`):
`maxHeartbeats` (kernel heartbeat limit in thousands, default 0 = none), `maxRecDepth`, `native`
(run the oracle, default true), `wf` (well-founded recursion transform, default true), `split`
(check in up to this many kernel declarations along `&&`/`List.all`, default 1), `opt`
(experimental inlining, default false).
-/

open Lean Meta Elab Tactic

namespace NativeTrust

/-- Configuration for `kdecide`. -/
structure KDecideConfig where
  maxHeartbeats : Nat := 0
  maxRecDepth : Nat := 100000
  native : Bool := true
  wf : Bool := true
  opt : Bool := false
  diagnoseFalse : Bool := true
  split : Nat := 1

def KDecideConfig.toKernelConfig (c : KDecideConfig) : KernelConfig :=
  { maxHeartbeats := c.maxHeartbeats, maxRecDepth := c.maxRecDepth, native := c.native,
    wf := c.wf, opt := c.opt, diagnoseFalse := c.diagnoseFalse, split := c.split }

declare_config_elab elabKDecideConfig KDecideConfig

/-- `kdecide` proves a closed decidable proposition by evaluating its decision procedure in
Lean's kernel. Unlike `native_decide` it adds no axiom: the result depends only on `propext`,
`Classical.choice` and `Quot.sound`. Well-founded recursion, which `decide +kernel` cannot
evaluate, is handled automatically. -/
syntax (name := kdecide) "kdecide" Lean.Parser.Tactic.optConfig : tactic

/-- Prove the closed decidable proposition `p` by kernel evaluation; returns the proof term. -/
def kdecideCore (p : Expr) (cfg : KernelConfig) : TermElabM Expr := do
  let mut p ← instantiateMVars p
  if p.hasFVar then p ← zetaReduce p
  if p.hasMVar then throwError "kdecide: the goal must not contain metavariables{indentExpr p}"
  if p.hasFVar then throwError "kdecide: the goal must not contain free variables{indentExpr p}"
  let inst ← synthInstance (mkApp (mkConst ``Decidable) p)
  let e := mkApp2 (mkConst ``Decidable.decide) p inst
  let mut native? : Option Bool := none
  if cfg.native then
    match ← nativeEval e with
    | .ok false => throwError "kdecide: compiled evaluation says the proposition is false{indentExpr p}"
    | .ok b => native? := some b
    | .error msg => logInfo m!"kdecide: compiled evaluation unavailable ({msg}); using the kernel only"
  let levelsInType := (collectLevelParams {} p).params
  let lvls := (← Term.getLevelNames).reverse.filter levelsInType.contains
  let name ← mkAuxDeclName `_kdecide
  let r ← proveTrueSplit e name lvls cfg native?
  return mkApp3 (mkConst ``of_decide_eq_true) p inst (mkConst r.thm (lvls.map mkLevelParam))

@[tactic kdecide] def evalKDecide : Tactic := fun stx => do
  let cfg ← elabKDecideConfig stx[1]
  closeMainGoalUsing `kdecide fun expectedType _ => kdecideCore expectedType cfg.toKernelConfig

end NativeTrust
