import Lean
import Strata.Languages.Core.Factory
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["Core.Expression", "Core.FactoryFuncNames", "Core.WFFactoryArray", "Core.isNameInFactory", "Core.seqAppendFunc", "Core.seqBuildFunc", "Core.seqDropFunc", "Core.seqDropUnsafeFunc", "Core.seqTakeFunc", "Core.seqTakeUnsafeFunc", "Core.seqUpdateFunc", "Core.seqUpdateUnsafeFunc", "Lambda.Constraint.unifyOne._mutual", "Lambda.Constraints.unify", "Lambda.Constraints.unifyCore", "Lambda.LExpr.eval", "Lambda.LExpr.eval._mutual", "Lambda.LExpr.evalFully", "Lambda.LFunc.computeTypeSubst", "Lambda.LFunc.opTypeSubst", "_private.Strata.Languages.Core.Factory.0.Core.renameOpIn", "_private.Strata.Languages.Core.Factory.0.Core.withSelectBang"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
