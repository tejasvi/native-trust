import G_Veir_Passes_RISCVCombines_Combine_29
import Veir.Passes.RISCVCombines.Combine
open Lean in
def parse (s : String) : Lean.Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Lean.Name.mkNum n k | none => Lean.Name.mkStr n c) Lean.Name.anonymous
#print axioms bvs5fact_29.unsat
open Lean in
#eval show MetaM Unit from do
  pure ()
