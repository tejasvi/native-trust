import Lean
import CpcMini.Proofs.CheckerCore
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["Eo.__eo_typeof", "Eo.__eo_typeof._f", "Eo.__eo_typeof_dt_cons_rec", "Eo.__eo_typeof_dt_cons_rec._unary", "Eo.__eo_typeof_dt_sel_return", "Eo.__eo_typeof_dt_sel_return._unary"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
