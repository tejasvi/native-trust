import G_Clean_Gadgets_Or_Or8_0
import Clean.Gadgets.Or.Or8
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
  IO.println s!"TYPE\tbvs5_1\t{(← getConstInfo (parse "bvs5_1")).type == (← getConstInfo (parse "_private.Clean.Gadgets.Or.Or8.0.Gadgets.Or.Or8.or_times_two_sub_xor")).type}"
  IO.println s!"TYPE\tbvs5_2\t{(← getConstInfo (parse "bvs5_2")).type == (← getConstInfo (parse "_private.Clean.Gadgets.Or.Or8.0.Gadgets.Or.Or8.two_or_ge_add")).type}"
  IO.println s!"TYPE\tbvs5_3\t{(← getConstInfo (parse "bvs5_3")).type == (← getConstInfo (parse "_private.Clean.Gadgets.Or.Or8.0.Gadgets.Or.Or8.or_times_two_sub_xor'")).type}"
  IO.println s!"TYPE\tbvs5_4\t{(← getConstInfo (parse "bvs5_4")).type == (← getConstInfo (parse "Gadgets.Or.Or8.completeness")).type}"
  IO.println s!"TYPE\tbvs5_5\t{(← getConstInfo (parse "bvs5_5")).type == (← getConstInfo (parse "Gadgets.Or.Or8.soundness")).type}"
  IO.println s!"TYPE\tbvs5_6\t{(← getConstInfo (parse "bvs5_6")).type == (← getConstInfo (parse "Gadgets.Or.Or8.circuit")).type}"
