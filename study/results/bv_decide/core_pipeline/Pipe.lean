import BitsKernel
/-! Where does the kernel spend its time in the CNF pipeline? (s4: 312 AIG nodes, 731 clauses) -/
set_option Elab.async false
set_option maxHeartbeats 0
open Lean Meta Elab Command Std.Tactic.BVDecide LratBits

theorem s4 (x y : BitVec 16) : (x &&& y) + (x ||| y) = x + y := by bv_decide

attribute [local instance high] KC.Std.Tactic.BVDecide.instHashableBVBit

elab "kb_eval " t:term : command => liftTermElabM do
  let e ← Term.elabTerm t (some (mkConst ``Bool))
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let r ← NativeTrust.proveTrueByKernel e (← mkAuxDeclName `kbeval) [] { native := false, trace := false, diagnoseFalse := false }
  IO.eprintln s!"eval {r.ms} ms"

kb_eval (KC.Std.Tactic.BVDecide.BVLogicalExpr.bitblast s4._expr_def_1).aig.decls.size == 312
kb_eval (KC.Std.Sat.AIG.Entrypoint.relabelNat (KC.Std.Tactic.BVDecide.BVLogicalExpr.bitblast s4._expr_def_1)).aig.decls.size == 312
kb_eval cnfSum (toL (KC.Std.Sat.AIG.toCNF (KC.Std.Sat.AIG.Entrypoint.relabelNat (KC.Std.Tactic.BVDecide.BVLogicalExpr.bitblast s4._expr_def_1)))) == 258414
