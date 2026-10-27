import NativeTrust
open NativeTrust
set_option Elab.async false

def isPrime (n : Nat) : Bool := n ≥ 2 && (List.range (n - 2)).all fun i => n % (i + 2) != 0
def checkAll (l : List Nat) : Bool := l.all fun n => isPrime n || n % 2 == 0 || n % 3 == 0 || n % 5 == 0 || n % 7 == 0 || n ≥ 0

theorem sp1 : checkAll [2, 3, 5, 7, 11, 13, 17, 19, 23, 29, 31, 37] = true := by kdecide (config := { split := 4 })
#print axioms sp1
#print sp1
theorem sp2 : (isPrime 97 && isPrime 89) && isPrime 83 = true := by kdecide (config := { split := 3 })
#print axioms sp2
theorem sp3 : ∀ x ∈ [97, 89, 83, 79], isPrime x = true := by kdecide (config := { split := 4 })
#print axioms sp3
open Lean in
run_cmd Elab.Command.liftTermElabM do
  let env ← getEnv
  for root in [`sp1._kdecide_1, `sp2._kdecide_1, `sp3._kdecide_1] do
    let mut ps := #[]
    for i in [0:10] do
      let n := root ++ (`p).appendIndexAfter i
      if env.contains n then ps := ps.push n
    logInfo m!"{root}: {ps.size} pieces"
