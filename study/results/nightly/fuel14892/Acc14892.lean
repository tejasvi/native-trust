import NativeTrust

/-! On a toolchain with lean4 PR #14892 (well-founded recursion without large elimination of
`Acc`): the fuel route converts well-founded functions, the accessibility-generator route cannot. -/

set_option Elab.async false

theorem n1 : (List.range 60).reverse.mergeSort = List.range 60 := by native_decide

def lexAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => lexAck m 1
  | m + 1, n + 1 => lexAck m (lexAck (m + 1) n)
termination_by m n => (m, n)

theorem n2 : lexAck 2 3 = 9 := by native_decide

kernelize n1 as n1_acc (config := { wfAcc := true })
