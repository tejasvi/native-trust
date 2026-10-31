import Lean
import Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecToInt
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["Eo.__eo_list_repeat", "Eo.__eo_list_repeat_rec", "Eo.__eo_list_repeat_rec._f", "Eo.__eo_list_singleton_intro", "Eo.__run_evaluate", "Eo.__run_evaluate._f", "Eo.__str_collect", "Eo.__str_collect._f", "Eo.__str_flatten", "Eo.__str_flatten._f", "_private.Cpc.Proofs.RuleSupport.Evaluate.Prelude.BitVecToInt.0.EvaluateProofInternal.eo_eval_sbv_to_int_rhs"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
