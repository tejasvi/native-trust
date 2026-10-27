import Mathlib.Data.Nat.Prime.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.Basic
import NativeTrust
open NativeTrust
set_option Elab.async false

theorem m1 : Nat.Prime 97 := by kdecide
theorem m2 : (Finset.range 10).sum id = 45 := by kdecide
theorem m3 : (3 : ZMod 7) * 5 = 1 := by kdecide
theorem m4 : ∀ x : Fin 5, x * x ≠ 2 := by kdecide
theorem m5 : Nat.factorial 10 = 3628800 := by kdecide
theorem m6 : ((Finset.range 100).filter Nat.Prime).card = 25 := by kdecide
open Lean in
run_cmd Elab.Command.liftTermElabM do
  for n in [``m1, ``m2, ``m3, ``m4, ``m5, ``m6] do
    let axs ← collectAxioms n
    logInfo m!"{n}: {if axs.contains ``sorryAx then "FAILED" else "ok"} {axs.toList}"
