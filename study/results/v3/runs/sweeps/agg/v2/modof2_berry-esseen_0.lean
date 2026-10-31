import Lean
import BerryEsseen.Upper0423.Covers.Data.BE3
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["BerryEsseen.Upper0423.Covers.Data.BE3.data", "BerryEsseen.Upper0423.Native.coverStringAcceptedBE", "BerryEsseen.Upper0423.Native.parseCover", "BerryEsseen.Upper0423.Native.parseCover._f", "BerryEsseen.Upper0423.Native.parseEnds", "BerryEsseen.Upper0423.Native.parseEnds._f", "BerryEsseen.Upper0423.Native.parseNat", "BerryEsseen.Upper0423.Native.parsePanels", "BerryEsseen.Upper0423.Native.parsePanels._f", "BerryEsseen.Upper0423.Native.parseRat", "BerryEsseen.Upper0423.Native.tokens", "String.Slice.toInt?", "String.Slice.toNat?", "String.splitOn", "String.splitOnAux", "String.splitOnAux._unary", "String.toInt?", "String.toNat?"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
