import VC_ISel
import Veir.Passes.InstructionSelection.Proofs
#print axioms bvs5fact_12.unsat
#print axioms bvs5fact_25.unsat
#print axioms bvs5_1
#print axioms bvs5_2
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n c) Name.anonymous
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE_IDENTICAL bvs5_1 Veir.Data.RISCV.bitreverse_refinement {(← getConstInfo (parseN "bvs5_1")).type == (← getConstInfo (parseN "Veir.Data.RISCV.bitreverse_refinement")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_2 Veir.Data.RISCV.bitreverse_refinement_32 {(← getConstInfo (parseN "bvs5_2")).type == (← getConstInfo (parseN "Veir.Data.RISCV.bitreverse_refinement_32")).type}"
  pure ()
