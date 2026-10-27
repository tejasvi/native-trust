import NativeTrust

/-! `linter.nativeTrust`: the "unnecessary" check (plain kernel evaluation within
`nativeTrust.kernelHeartbeats`) next to the static blocked-construct warning. -/

set_option linter.nativeTrust true

/-- `decide +kernel` proves it: warning and a `decide +kernel` suggestion at the tactic -/
theorem lk_sum : (List.range 100).foldl (· + ·) 0 = 4950 := by native_decide

/-- the same for `decide +native` -/
theorem lk_sum2 : (List.range 50).foldl (· + ·) 0 = 1225 := by decide +native

def sumTok (l : List String) (i : Nat) : Nat :=
  if h : i < l.length then (l[i].toNat?.getD 0) + sumTok l (i + 1) else 0
termination_by l.length - i

/-- `String.toNat?` runs on an iterator loop; NativeTrust's string replacements (`NativeTrust.StrLib`)
make it convertible, so no blocked-construct warning (on Lean 4.27-4.29, whose `StrLib` is a stub, it
stays blocked) -/
theorem lk_str : sumTok ["1", "2", "3"] 0 = 6 := by native_decide

/-- `Std.HashMap` computes bucket indices in `USize`, whose width is the opaque
`System.Platform.getNumBits`, so `decide +kernel` fails (no "unnecessary" warning). It is the only such
constant, and NativeTrust's platform case split converts the fact: no blocked-construct warning either -/
theorem lk_blocked : ((∅ : Std.HashMap Nat Nat).insert 1 2).size = 1 := by native_decide

/-- the word size itself: the static triage cannot tell it from `lk_blocked` (no warning); the audit tries
the case split, which fails, and reports it blocked -/
theorem lk_word : System.Platform.numBits = 64 := by native_decide

/-- over the budget (2000 thousand heartbeats, about 1.4 s here): no warning -/
theorem lk_budget : (List.range 100000).foldl (· + ·) 0 = 4999950000 := by native_decide

/-- one tactic call, two facts: one warning for the call -/
theorem lk_two : (List.range 10).length = 10 ∧ (List.range 20).length = 20 := by
  constructor <;> native_decide

def lexAck : Nat → Nat → Nat
  | 0, n => n + 1
  | m + 1, 0 => lexAck m 1
  | m + 1, n + 1 => lexAck m (lexAck (m + 1) n)
termination_by m n => (m, n)

/-- well-founded recursion: plain kernel evaluation is stuck (`WellFounded.fix`), no warning -/
theorem lk_wf : lexAck 2 3 = 9 := by native_decide

-- the check can be switched off
set_option linter.nativeTrust.unnecessary false in
theorem lk_off : (List.range 30).length = 30 := by native_decide

#native_decide_audit
