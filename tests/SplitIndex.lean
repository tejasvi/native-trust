import NativeTrust
open NativeTrust
set_option Elab.async false
def isPrime (n : Nat) : Bool := n ≥ 2 && (List.range (n - 2)).all fun i => n % (i + 2) != 0
-- a computed list (not an explicit literal)
theorem si1 : (List.range 40).all (fun n => isPrime (n + 100) || n % 2 == 0 || n % 3 == 0 || n ≥ 0) = true := by
  kdecide (config := { split := 4 })
#print axioms si1
-- statement shape of certificate checks: decide (computed.all check = true)
theorem si2 : ((List.range 30).map (· * 7)).all (fun n => n % 7 == 0) = true := by
  kdecide (config := { split := 3 })
open Lean in
run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  for root in [`si1._kdecide_1, `si2._kdecide_1] do
    let ps := (List.range 10).filter fun i => env.contains (root ++ (`p).appendIndexAfter i)
    logInfo m!"{root}: {ps.length} pieces"
