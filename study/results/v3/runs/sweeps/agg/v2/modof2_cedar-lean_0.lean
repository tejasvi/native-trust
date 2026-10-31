import Lean
import UnitTest.Decimal
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["Cedar.Spec.Ext.Decimal.parse", "Cedar.Spec.Ext.toInt?'", "Cedar.Spec.Ext.toNat?'", "String.Slice.toInt?", "String.Slice.toNat?", "String.toInt?", "String.toNat?"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
