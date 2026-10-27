import NativeTrust

/-! A blocker reachable only through a kernel-reducible copy (`sumTok` is well-founded, so it is
copied; `String.toNat?` is reached through the copy's definition). -/

def sumTok (l : List String) (i : Nat) : Nat :=
  if h : i < l.length then (l[i].toNat?.getD 0) + sumTok l (i + 1) else 0
termination_by l.length - i

theorem t3 : sumTok ["1", "2", "3"] 0 = 6 := by native_decide

#kernel_blockers t3
#kernel_blockers_const sumTok
trust_check t3
