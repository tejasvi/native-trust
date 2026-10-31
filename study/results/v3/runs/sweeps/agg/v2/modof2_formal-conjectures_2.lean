import Lean
import FormalConjectures.OEIS.«41»
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["CompositionAsSet.blocks", "CompositionAsSet.blocksFun", "CompositionAsSet.boundary", "CompositionAsSet.toComposition", "Finset.orderEmbOfFin", "Finset.orderIsoOfFin", "Nat.Partition.instFintype", "Nat.instDecidableEqPartition", "Nat.partitionNumber", "compositionEquiv", "compositionFintype"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
