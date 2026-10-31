import G_Clean_Gadgets_And_And8_0
import Clean.Gadgets.And.And8
open Lean in
def parse (s : String) : Lean.Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Lean.Name.mkNum n k | none => Lean.Name.mkStr n c) Lean.Name.anonymous
#print axioms bvs5fact_0.unsat
#print axioms bvs5_1
#print axioms bvs5_2
#print axioms bvs5_3
#print axioms bvs5_4
#print axioms bvs5_5
#print axioms bvs5_6
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE\tbvs5_1\t{(← getConstInfo (parse "bvs5_1")).type == (← getConstInfo (parse "Gadgets.And.And8.and_times_two_add_xor")).type}"
  IO.println s!"TYPE\tbvs5_2\t{(← getConstInfo (parse "bvs5_2")).type == (← getConstInfo (parse "Gadgets.And.And8.xor_le_add")).type}"
  IO.println s!"TYPE\tbvs5_3\t{(← getConstInfo (parse "bvs5_3")).type == (← getConstInfo (parse "Gadgets.And.And8.soundness")).type}"
  IO.println s!"TYPE\tbvs5_4\t{(← getConstInfo (parse "bvs5_4")).type == (← getConstInfo (parse "Gadgets.And.And8.two_and_le_add")).type}"
  IO.println s!"TYPE\tbvs5_5\t{(← getConstInfo (parse "bvs5_5")).type == (← getConstInfo (parse "Gadgets.And.And8.completeness")).type}"
  IO.println s!"TYPE\tbvs5_6\t{(← getConstInfo (parse "bvs5_6")).type == (← getConstInfo (parse "Gadgets.And.And8.circuit")).type}"
