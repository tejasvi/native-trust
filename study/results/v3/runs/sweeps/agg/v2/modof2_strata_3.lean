import Lean
import StrataTest.Languages.Core.Tests.Logic.HoareUnstructured
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["Core.DetCFG", "Core.instProcedureHeaderExpressionHeader", "_ktr.F2_StrataTest_Languages_Core_Tests_Logic_HoareUnstructured_11.Core.Factory", "_ktr.F2_StrataTest_Languages_Core_Tests_Logic_HoareUnstructured_11.Core.WFFactory", "_private.StrataTest.Languages.Core.Tests.Logic.HoareUnstructured.0.Strata.copyCFG", "_private.StrataTest.Languages.Core.Tests.Logic.HoareUnstructured.0.Strata.copyPgm", "_private.StrataTest.Languages.Core.Tests.Logic.HoareUnstructured.0.Strata.copyPgmSrc", "_private.StrataTest.Languages.Core.Tests.Logic.HoareUnstructured.0.Strata.cstToAST", "_private.StrataTest.Languages.Core.Tests.Logic.HoareUnstructured.0.Strata.falseEnsPgm", "_private.StrataTest.Languages.Core.Tests.Logic.HoareUnstructured.0.Strata.falseEnsPgmSrc", "_private.StrataTest.Languages.Core.Tests.Logic.HoareUnstructured.0.Strata.sumToNCFG.match_1"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
