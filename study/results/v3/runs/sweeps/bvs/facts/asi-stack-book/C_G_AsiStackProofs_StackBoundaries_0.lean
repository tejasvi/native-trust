import G_AsiStackProofs_StackBoundaries_0
import AsiStackProofs.StackBoundaries
open Lean in
def parse (s : String) : Lean.Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Lean.Name.mkNum n k | none => Lean.Name.mkStr n c) Lean.Name.anonymous
#print axioms bvs5fact_0.unsat
#print axioms bvs5_1
#print axioms bvs5_2
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE\tbvs5_1\t{(← getConstInfo (parse "bvs5_1")).type == (← getConstInfo (parse "AsiStackProofs.StackBoundaries.admitted_layer_contract_is_complete")).type}"
  IO.println s!"TYPE\tbvs5_2\t{(← getConstInfo (parse "bvs5_2")).type == (← getConstInfo (parse "AsiStackProofs.StackBoundaries.unauthorized_external_action_cannot_be_admitted")).type}"
