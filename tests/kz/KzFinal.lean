import NativeTrust
import KzNative
set_option Elab.async false
kernelize sorted_check as sorted_check_k
def ack : Nat → Nat → Nat
  | 0, n => n + 1
  | m+1, 0 => ack m 1
  | m+1, n+1 => ack m (ack (m+1) n)
termination_by m n => (m, n)
theorem msort_k : (List.range 200).reverse.mergeSort = List.range 200 ∧ ack 2 2 = 7 := by kdecide (config := { split := 2 })
