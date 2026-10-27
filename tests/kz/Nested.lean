import NativeTrust

/-! Nested native facts: a definition carries a `native_decide` proof, and a native fact (and the
theorem's statement) mention that definition. -/

structure Ledger where
  atoms : Nat
  even : atoms % 2 = 0

def ledger : Ledger := ⟨(List.range 10).foldl (· + ·) 0 + 1, by native_decide⟩

theorem nested : ledger.atoms = 46 := by native_decide

theorem nested_use : ledger.atoms + 1 = 47 := by rw [nested]

trust_check nested
trust_check nested_use
#print axioms nested.kernel
#print axioms nested_use.kernel
example : nested.kernel = nested.kernel := rfl
