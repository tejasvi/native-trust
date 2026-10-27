import NativeTrust

set_option linter.nativeTrust true

/-- kernel-checkable: no warning -/
theorem ok1 : (List.range 100).foldl (· + ·) 0 = 4950 := by native_decide

def sumTok (l : List String) (i : Nat) : Nat :=
  if h : i < l.length then (l[i].toNat?.getD 0) + sumTok l (i + 1) else 0
termination_by l.length - i

/-- native-only: the linter names `String.toNat?`'s iterator loop -/
theorem bad1 : sumTok ["1", "2", "3"] 0 = 6 := by native_decide
