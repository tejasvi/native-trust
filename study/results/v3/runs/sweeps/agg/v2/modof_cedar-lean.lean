import UnitTest.Decimal
import UnitTest.IPAddr
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["Cedar.Spec.Ext.Decimal.parse", "Cedar.Spec.Ext.IPAddr.ip", "Cedar.Spec.Ext.toInt?'", "Cedar.Spec.Ext.toNat?'", "String.Slice.Pos.skipWhile", "String.Slice.Pos.skipWhile._unary", "String.Slice.all", "String.Slice.skipPrefixWhile", "String.Slice.toInt?", "String.Slice.toNat?", "String.all", "String.foldl", "String.splitOn", "String.splitOnAux", "String.splitOnAux._unary", "String.toInt?", "String.toNat?", "_private.Cedar.Spec.Ext.IPAddr.0.Cedar.Spec.Ext.IPAddr.parse", "_private.Cedar.Spec.Ext.IPAddr.0.Cedar.Spec.Ext.IPAddr.parseIPv4Net", "_private.Cedar.Spec.Ext.IPAddr.0.Cedar.Spec.Ext.IPAddr.parseIPv6Net", "_private.Cedar.Spec.Ext.IPAddr.0.Cedar.Spec.Ext.IPAddr.parseNumSegsV6", "_private.Cedar.Spec.Ext.IPAddr.0.Cedar.Spec.Ext.IPAddr.parseNumV4", "_private.Cedar.Spec.Ext.IPAddr.0.Cedar.Spec.Ext.IPAddr.parseNumV6", "_private.Cedar.Spec.Ext.IPAddr.0.Cedar.Spec.Ext.IPAddr.parsePrefixNat", "_private.Cedar.Spec.Ext.IPAddr.0.Cedar.Spec.Ext.IPAddr.parseSegsV4", "_private.Cedar.Spec.Ext.IPAddr.0.Cedar.Spec.Ext.IPAddr.parseSegsV6"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
