import NativeTrust

/-! Negative controls for `Fuel14892.lean`, in a file of their own: there `n1_acc` reuses the proof that
`n1_fuel` registered, so it is no test of the old route. On a toolchain with lean4 PR #14892 both
commands below should fail; on Lean ≤ 4.36 the accessibility-generator route should succeed and
`decide +kernel` should still fail (`WellFounded.fix (Lean.opaqueId wf) F` does not unfold). -/

set_option Elab.async false

theorem n1 : (List.range 60).reverse.mergeSort = List.range 60 := by native_decide

kernelize n1 as n1_acc (config := { wfAcc := true, accFallback := false })

theorem n1_core : (List.range 60).reverse.mergeSort = List.range 60 := by decide +kernel
