/-! Native facts for the per-axiom commands: one inside a definition (inner), one whose statement
mentions that definition, one in a theorem. -/

structure Ledger where
  atoms : Nat
  even : atoms % 2 = 0

def ledger : Ledger := ⟨(List.range 10).foldl (· + ·) 0 + 1, by native_decide⟩

theorem nested : ledger.atoms = 46 := by native_decide

theorem plain : (List.range 100).foldl (· + ·) 0 = 4950 := by native_decide
