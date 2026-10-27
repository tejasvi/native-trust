import VC_Examples
import Veir.Data.PBV.Examples
#print axioms bvs5fact_0.unsat
#print axioms bvs5fact_1.unsat
#print axioms bvs5fact_2.unsat
#print axioms bvs5fact_3.unsat
#print axioms bvs5fact_4.unsat
#print axioms bvs5_1
#print axioms bvs5_2
#print axioms bvs5_3
#print axioms bvs5_4
#print axioms bvs5_5
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n c) Name.anonymous
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE_IDENTICAL bvs5_1 _private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_zero_zero_extend_conj {(← getConstInfo (parseN "bvs5_1")).type == (← getConstInfo (parseN "_private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_zero_zero_extend_conj")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_2 _private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_zero_zero_extend {(← getConstInfo (parseN "bvs5_2")).type == (← getConstInfo (parseN "_private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_zero_zero_extend")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_3 _private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_add_comm_manual {(← getConstInfo (parseN "bvs5_3")).type == (← getConstInfo (parseN "_private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_add_comm_manual")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_4 _private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_zero_sign_extend {(← getConstInfo (parseN "bvs5_4")).type == (← getConstInfo (parseN "_private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_zero_sign_extend")).type}"
  IO.println s!"TYPE_IDENTICAL bvs5_5 _private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_append {(← getConstInfo (parseN "bvs5_5")).type == (← getConstInfo (parseN "_private.Veir.Data.PBV.Examples.0.Veir.Data.PBV.trace_append")).type}"
  pure ()
