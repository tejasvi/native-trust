import G_Veir_Data_PBV_Examples_2
import Veir.Data.PBV.Examples
open Lean in
def parse (s : String) : Lean.Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Lean.Name.mkNum n k | none => Lean.Name.mkStr n c) Lean.Name.anonymous
#print axioms bvs5fact_2.unsat
#print axioms bvs5_1
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE\tbvs5_1\t{(← getConstInfo (parse "bvs5_1")).type == (← getConstInfo (parse "_private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_add_comm_manual")).type}"
