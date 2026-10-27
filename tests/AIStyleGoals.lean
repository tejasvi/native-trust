import Mathlib.NumberTheory.Padics.PadicVal.Basic
import Mathlib.Data.Nat.Factorization.Basic
import Mathlib.NumberTheory.Divisors
import Mathlib.Algebra.BigOperators.Intervals
import Mathlib.Data.ZMod.Basic
import NativeTrust
open NativeTrust
set_option Elab.async false
set_option maxRecDepth 100000
-- Analogues of the goal kinds found in AI-prover corpora (not the corpus files themselves)
theorem g1 : (24 : ZMod 121)⁻¹ = 116 := by kdecide
theorem g2 : ∑ i ∈ Finset.Icc 1 100, i = 5050 := by kdecide
theorem g3 : ∑ d ∈ Nat.divisors 360, d = 1170 := by kdecide
theorem g4 : ((Finset.range 1000).filter (fun n => n % 7 = 3)).card = 143 := by kdecide
theorem g5 : padicValNat 2 1024 = 10 := by kdecide
theorem g6 : Nat.factorization 360 2 = 3 := by kdecide
theorem g7 : Nat.factorial 13 % 1001 = 0 := by kdecide
theorem g8 : ∀ x : ZMod 13, x ^ 12 = 1 ∨ x = 0 := by kdecide
open Lean in
run_cmd Elab.Command.liftTermElabM do
  for n in [``g1, ``g2, ``g3, ``g4, ``g5, ``g6, ``g7, ``g8] do
    let axs ← collectAxioms n
    logInfo m!"{n}: {if axs.contains ``sorryAx then "FAILED" else "ok"} {axs.toList}"
