import Lean
import Cpc.Proofs.RuleSupport.ArithStringEntailSupport
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["Smtm.__smtx_ret_typeof_sel", "Smtm.__smtx_ret_typeof_sel_rec", "Smtm.__smtx_ret_typeof_sel_rec._unary", "Smtm.__smtx_typeof", "Smtm.__smtx_typeof._f", "Smtm.__smtx_typeof_dt_cons_rec", "Smtm.__smtx_typeof_dt_cons_rec._unary", "Smtm.__smtx_typeof_guard_wf", "Smtm.__smtx_typeof_seq_nth", "__eo_to_smt", "__eo_to_smt._f", "__eo_to_smt_datatype_decl", "__eo_to_smt_exists", "__eo_to_smt_exists._f", "__eo_to_smt_quantifiers_skolemize", "__eo_to_smt_quantifiers_skolemize._f", "__eo_to_smt_tuple_prepend", "__eo_to_smt_tuple_prepend_of_type", "__eo_to_smt_type", "__eo_to_smt_type._f", "__eo_to_smt_type_tuple", "__eo_to_smt_typed_list_elem_type._f"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
