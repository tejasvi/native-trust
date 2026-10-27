import NativeTrust

set_option nativeTrust.eprint true

def sumTok (l : List String) (i : Nat) : Nat :=
  if h : i < l.length then (l[i].toNat?.getD 0) + sumTok l (i + 1) else 0
termination_by l.length - i

theorem t3 : sumTok ["1", "2", "3"] 0 = 6 := by native_decide

def lexAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => lexAck m 1
  | m + 1, n + 1 => lexAck m (lexAck (m + 1) n)
termination_by m n => (m, n)

theorem ack : lexAck 2 3 = 9 := by native_decide

#kernel_blockers t3
#kernel_blockers ack
trust_check ack (config := { trace := true })
trust_check t3 (config := { trace := true })
