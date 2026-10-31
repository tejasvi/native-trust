import FormalConjectures.ErdosProblems.«340»
import FormalConjectures.OEIS.«237271»
import FormalConjectures.OEIS.«41»
import FormalConjectures.WrittenOnTheWallII.Test
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["CompositionAsSet.blocks", "CompositionAsSet.blocksFun", "CompositionAsSet.boundary", "CompositionAsSet.toComposition", "Finset.greedySidon", "Finset.greedySidon.aux", "Finset.greedySidon.aux._f", "Finset.orderEmbOfFin", "Finset.orderIsoOfFin", "Finset.sort", "List.merge", "List.merge._unary", "List.mergeSort", "List.mergeSort._unary", "Nat.Partition.instFintype", "Nat.find", "Nat.findX", "Nat.instDecidableEqPartition", "Nat.partitionNumber", "OeisA237271.a", "SimpleGraph.havelHakimiStep", "compositionEquiv", "compositionFintype"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
