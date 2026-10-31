import Lean
import IChO2026Problems.problem_icho_2026_t8_a3
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["IChO2026Problems.ProblemIcho2026T8A3.exactCatalystFigureEvidence", "IChO2026Problems.ProblemIcho2026T8A3.exactFeQpyLiterature", "IChO2026Problems.ProblemIcho2026T8A3.qpyBasalAxialLiterature", "IChO2026Problems.ProblemIcho2026T8A3.qpyBasalAxialTopologyEvidence"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
