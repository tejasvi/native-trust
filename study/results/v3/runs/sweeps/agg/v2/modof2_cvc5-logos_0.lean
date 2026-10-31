import Lean
import Cpc.Proofs.RuleSupport.ArithPolyNormSupport
open Lean in
def parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with | some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous
open Lean in
#eval show CoreM Unit from do
  let env ← getEnv
  for s in ["Eo.__get_arith_poly_norm", "Eo.__get_arith_poly_norm._f", "Eo.__mon_mul_mon", "Eo.__mvar_mul_mvar", "Eo.__mvar_mul_mvar._unary", "Eo.__poly_add", "Eo.__poly_add._unary", "Eo.__poly_mul", "Eo.__poly_mul._f", "Eo.__poly_mul_mon", "Eo.__poly_mul_mon._f"] do
    match env.getModuleIdxFor? (parseN s) with
    | some i => IO.println s!"MODOF\t{s}\t{env.header.moduleNames[i.toNat]!}"
    | none => IO.println s!"MODOF\t{s}\t-"
