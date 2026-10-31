import IChO2026Problems.problem_icho_2026_t3_a5
import IChO2026Problems.problem_icho_2026_t6_a2
import IChO2026Problems.problem_icho_2026_t8_a3
import IChO2026Problems.problem_icho_2026_t8_a4
import IChO2026Problems.problem_icho_2026_t9_a3
import IChO2026Problems.problem_icho_2026_t9_a5
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["IChO2026Problems.Icho2026T3A5.TransformationAuthority.reference", "IChO2026Problems.Icho2026T3A5.imineOxidationReference", "IChO2026Problems.Icho2026T3A5.reductiveOzonolysisReference", "IChO2026Problems.Icho2026T9A3.acetylationLawEvidence", "IChO2026Problems.Icho2026T9A3.borohydrideLawEvidence", "IChO2026Problems.Icho2026T9A3.periodateLawEvidence", "IChO2026Problems.Icho2026T9A3.xReactionLawLedger", "IChO2026Problems.ProblemIChO2026T8A4.complex10", "IChO2026Problems.ProblemIChO2026T8A4.complex11", "IChO2026Problems.ProblemIChO2026T8A4.complex12", "IChO2026Problems.ProblemIChO2026T8A4.complex13", "IChO2026Problems.ProblemIChO2026T8A4.complex14", "IChO2026Problems.ProblemIChO2026T8A4.complex15", "IChO2026Problems.ProblemIChO2026T8A4.derivedComplex", "IChO2026Problems.ProblemIChO2026T8A4.feQpyMechanismLiterature", "IChO2026Problems.ProblemIcho2026T8A3.exactCatalystFigureEvidence", "IChO2026Problems.ProblemIcho2026T8A3.exactFeQpyLiterature", "IChO2026Problems.ProblemIcho2026T8A3.qpyBasalAxialLiterature", "IChO2026Problems.ProblemIcho2026T8A3.qpyBasalAxialTopologyEvidence", "IChO2026Problems.T6A2.aLineDiagramReading", "IChO2026Problems.T6A2.bLineDiagramReading", "IChO2026Problems.T6A2.cLineDiagramReading", "IChO2026Problems.T6A2.dLineDiagramReading", "IChO2026Problems.T6A2.sunExtendedData12", "IChO2026Problems.T6A2.sunFigure4", "IChO2026Problems.T9A5.adBisDebenzylationAuthority", "IChO2026Problems.T9A5.perbenzylationAuthority"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
