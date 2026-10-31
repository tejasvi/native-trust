import Lean
import IChO2026Problems.problem_icho_2026_t6_a2
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["IChO2026Problems.T6A2.aLineDiagramReading", "IChO2026Problems.T6A2.bLineDiagramReading", "IChO2026Problems.T6A2.cLineDiagramReading", "IChO2026Problems.T6A2.dLineDiagramReading", "IChO2026Problems.T6A2.sunExtendedData12", "IChO2026Problems.T6A2.sunFigure4"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
