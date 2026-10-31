import G_Veir_Passes_InstructionSelection_Proofs_21
import Veir.Passes.InstructionSelection.Proofs
open Lean in
def parse (s : String) : Lean.Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Lean.Name.mkNum n k | none => Lean.Name.mkStr n c) Lean.Name.anonymous
#print axioms bvs5fact_21.unsat
#print axioms bvs5_1
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE\tbvs5_1\t{(← getConstInfo (parse "bvs5_1")).type == (← getConstInfo (parse "Veir.Data.RISCV.icmp_refinement_ugt_32")).type}"
