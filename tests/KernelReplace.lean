import NativeTrust
open NativeTrust
set_option Elab.async false

/-- Lexicographic termination: compiled to `WellFounded.fix … (Lean.opaqueId wf)`. -/
def f1 : Nat → Nat → Nat
  | 0, b => b
  | a+1, b => f1 a (b + 1)
termination_by a b => (a, b)

/-- The same recursion with a `Nat` measure: compiled to fuel (`WellFounded.Nat.fix`). -/
def f2 : Nat → Nat → Nat
  | 0, b => b
  | a+1, b => f2 a (b + 1)
termination_by a _ => a

theorem f1_eq_f2 : @f1 = @f2 := by
  funext a b
  induction a generalizing b with
  | zero => simp [f1, f2]
  | succ a ih => simp only [f1, f2]; exact ih (b + 1)

-- without the replacement, and without the accGen transform (as from Lean 4.37 on): stuck
example : f1 300 0 = 300 := by kdecide (config := { wf := false })

attribute [kernel_replace] f1_eq_f2

-- with the proof-carrying replacement: no reduction of proofs needed
theorem r1 : f1 300 0 = 300 := by kdecide (config := { wf := false })
#print axioms r1
