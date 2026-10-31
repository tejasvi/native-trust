import Lean
import CpcMini.Proofs.TypePreservation
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["Smtm.__smtx_decl_wf_rec._f", "Smtm.__smtx_dt_cons_wf_rec._f", "Smtm.__smtx_type_wf", "Smtm.__smtx_type_wf._f", "Smtm.__smtx_type_wf_component", "Smtm.__smtx_type_wf_rec", "Smtm.__smtx_type_wf_rec._f", "Smtm.__smtx_typeof_dt_cons_value_rec", "Smtm.__smtx_typeof_dt_cons_value_rec._unary", "Smtm.__smtx_typeof_value", "Smtm.__smtx_typeof_value._f", "Smtm.native_inhabited_type"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
