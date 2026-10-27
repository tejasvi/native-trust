import VA73_Final
import Veir.Passes.InstructionSelection.Proofs
#print axioms bvs5fact_73.unsat
#print axioms bvs5_1
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n c) Name.anonymous
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE_IDENTICAL bvs5_1 Veir.Data.RISCV.sshlSat_refinement {(← getConstInfo (parseN "bvs5_1")).type == (← getConstInfo (parseN "Veir.Data.RISCV.sshlSat_refinement")).type}"
  pure ()
