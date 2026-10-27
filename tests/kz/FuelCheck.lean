import NativeTrust

/-! Independent re-check of the fuel route: well-founded functions (lexicographic measures), proved
by kernel evaluation through `fixFuel` (no accessibility proof is reduced). -/

set_option Elab.async false

theorem fc_msort : (List.range 60).reverse.mergeSort = List.range 60 := by kdecide

def lexAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => lexAck m 1
  | m + 1, n + 1 => lexAck m (lexAck (m + 1) n)
termination_by m n => (m, n)

theorem fc_ack : lexAck 2 3 = 9 := by kdecide
