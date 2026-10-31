import Lean
import IChO2026Problems.problem_icho_2026_t8_a4
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["IChO2026Problems.ProblemIChO2026T8A4.complex10", "IChO2026Problems.ProblemIChO2026T8A4.complex11", "IChO2026Problems.ProblemIChO2026T8A4.complex12", "IChO2026Problems.ProblemIChO2026T8A4.complex13", "IChO2026Problems.ProblemIChO2026T8A4.complex14", "IChO2026Problems.ProblemIChO2026T8A4.complex15", "IChO2026Problems.ProblemIChO2026T8A4.derivedComplex", "IChO2026Problems.ProblemIChO2026T8A4.feQpyMechanismLiterature"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
