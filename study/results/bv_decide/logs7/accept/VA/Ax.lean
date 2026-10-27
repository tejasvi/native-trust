import VA_Final
import Veir.Passes.InstructionSelection.Proofs
#print axioms bvs5fact_73.unsat
#print axioms bvs5fact_88.unsat
#print axioms bvs5fact_89.unsat
#print axioms bvs5_1
#print axioms Veir.Data.RISCV.sdivwPow2_pos_refinement
#print axioms bvs5_2
#print axioms Veir.Data.RISCV.sdivwPow2_neg_refinement
#print axioms bvs5_3
#print axioms Veir.Data.RISCV.sshlSat_refinement
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE_IDENTICAL bvs5_1 Veir.Data.RISCV.sdivwPow2_pos_refinement {(← getConstInfo `bvs5_1).type == (← getConstInfo `Veir.Data.RISCV.sdivwPow2_pos_refinement).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_2 Veir.Data.RISCV.sdivwPow2_neg_refinement {(← getConstInfo `bvs5_2).type == (← getConstInfo `Veir.Data.RISCV.sdivwPow2_neg_refinement).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_3 Veir.Data.RISCV.sshlSat_refinement {(← getConstInfo `bvs5_3).type == (← getConstInfo `Veir.Data.RISCV.sshlSat_refinement).type}"
  pure ()
