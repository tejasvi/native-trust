import G_Veir_Passes_RISCVCombines_Combine_25
import Veir.Passes.RISCVCombines.Combine
open Lean in
def parse (s : String) : Lean.Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Lean.Name.mkNum n k | none => Lean.Name.mkStr n c) Lean.Name.anonymous
#print axioms bvs5fact_25.unsat
#print axioms bvs5_1
#print axioms bvs5_2
#print axioms bvs5_3
#print axioms bvs5_4
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE\tbvs5_1\t{(← getConstInfo (parse "bvs5_1")).type == (← getConstInfo (parse "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_packh._proof_1")).type}"
  IO.println s!"TYPE\tbvs5_2\t{(← getConstInfo (parse "bvs5_2")).type == (← getConstInfo (parse "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.sextw_packh")).type}"
  IO.println s!"TYPE\tbvs5_3\t{(← getConstInfo (parse "bvs5_3")).type == (← getConstInfo (parse "_private.Veir.Passes.RISCVCombines.Combine.0.Veir.RISCV.Combine.impl")).type}"
  IO.println s!"TYPE\tbvs5_4\t{(← getConstInfo (parse "bvs5_4")).type == (← getConstInfo (parse "Veir.RISCV.Combine")).type}"
