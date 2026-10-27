import VB15_Final
import Veir.Passes.InstructionSelection.Proofs
#print axioms bvs6fact_15.unsat
#print axioms bvs6_1
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n c) Name.anonymous
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE_IDENTICAL bvs6_1 Veir.Data.RISCV.sdivwPow2Exact_pos_refinement {(← getConstInfo (parseN "bvs6_1")).type == (← getConstInfo (parseN "Veir.Data.RISCV.sdivwPow2Exact_pos_refinement")).type}"
  pure ()
