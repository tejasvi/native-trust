import GNatuvea
import Proofs.Serialization
#print axioms bvsg_Model_CompositeHeader_0.unsat
#print axioms bvsg_Model_CompositeHeader_1.unsat
#print axioms bvsg_Proofs_Serialization_0.unsat
#print axioms bvsg_1
#print axioms bvsg_2
#print axioms bvsg_3
#print axioms bvsg_4
#print axioms bvsg_5
#print axioms bvsg_6
#print axioms bvsg_7
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n c) Name.anonymous
open Lean in
#eval show MetaM Unit from do
  IO.println s!"TYPE_IDENTICAL bvsg_1 Model.CompositeHeader.readBe16_be16 {(← getConstInfo (parseN "bvsg_1")).type == (← getConstInfo (parseN "Model.CompositeHeader.readBe16_be16")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_2 Model.CompositeHeader.readBe64_be64 {(← getConstInfo (parseN "bvsg_2")).type == (← getConstInfo (parseN "Model.CompositeHeader.readBe64_be64")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_3 Proofs.Serialization.readBe32_be32 {(← getConstInfo (parseN "bvsg_3")).type == (← getConstInfo (parseN "Proofs.Serialization.readBe32_be32")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_4 Proofs.Serialization.readBe32_be32_nil {(← getConstInfo (parseN "bvsg_4")).type == (← getConstInfo (parseN "Proofs.Serialization.readBe32_be32_nil")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_5 Proofs.Serialization.decode_encode_composite {(← getConstInfo (parseN "bvsg_5")).type == (← getConstInfo (parseN "Proofs.Serialization.decode_encode_composite")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_6 Proofs.Serialization.decodeBundle_encodeBundle {(← getConstInfo (parseN "bvsg_6")).type == (← getConstInfo (parseN "Proofs.Serialization.decodeBundle_encodeBundle")).type}"
  IO.println s!"TYPE_IDENTICAL bvsg_7 Proofs.Serialization.decode_encode {(← getConstInfo (parseN "bvsg_7")).type == (← getConstInfo (parseN "Proofs.Serialization.decode_encode")).type}"
  pure ()
