import BVS
/-!
# Axiom audit of the soundness theorems

Run with `lake env lean Audit.lean` after `lake build`. For each theorem, `#bvs_audit` prints its
axioms and those outside `propext`, `Classical.choice`, `Quot.sound` (expected: none). The file also
prints the statements of the end-to-end theorems and checks that their conclusion is core's
`Std.Tactic.BVDecide.BVLogicalExpr.Unsat`.
-/

open Lean Elab Command in
elab "#bvs_audit " ids:ident* : command => do
  for id in ids do
    let n := id.getId
    let some ci := (← getEnv).find? n | throwError "missing {n}"
    let axs ← liftCoreM <| collectAxioms n
    let std := #[``propext, ``Classical.choice, ``Quot.sound]
    let bad := axs.filter (fun a => !std.contains a)
    let kind := if ci matches .thmInfo _ then "theorem" else "other"
    logInfo m!"AUDIT {n}: axioms {axs.toList}; non-standard {bad.toList}; kind {kind}"

#bvs_audit BVS.unsat_of_cnf BVS.blastBool_spec BVS.blastUn_spec BVS.blastClz_spec BVS.blastCpop_spec
  BVS.bitsOf_reverse BVS.chkUR_sound BVS.bvs_unsat4 BVS.blastCk_sound BVS.agreeFrom_sound
  BVS.agreeSeg_sound BVS.wfEs_append BVS.gateLeaves_append BVS.acc_step BVS.bvs_unsat5

set_option pp.fullNames true in
#check @BVS.bvs_unsat4
set_option pp.fullNames true in
#check @BVS.bvs_unsat5
set_option pp.fullNames true in
#check @BVS.unsat_of_cnf

open Lean Elab Command in
#eval show CommandElabM Unit from do
  for n in [``BVS.bvs_unsat4, ``BVS.bvs_unsat5, ``BVS.unsat_of_cnf] do
    let ci ← getConstInfo n
    let ok := ci.type.getForallBody.isAppOf ``Std.Tactic.BVDecide.BVLogicalExpr.Unsat
    logInfo m!"AUDIT conclusion of {n} is Std.Tactic.BVDecide.BVLogicalExpr.Unsat: {ok}"
