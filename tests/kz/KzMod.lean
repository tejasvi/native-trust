module

/-! Module-system file: the axioms `native_decide` adds get private names; one private theorem,
one fact inside a definition (abstracted to an internal `_proof_i` theorem). -/

@[expose] public section

def primesBelow (n : Nat) : List Nat :=
  (List.range n).filter fun k => k ≥ 2 && (List.range k).all fun d => d < 2 || k % d != 0

theorem pub_count : (primesBelow 60).length = 17 := by native_decide

def seven : { n : Nat // n * n = 49 } := ⟨7, by native_decide⟩

end

private theorem priv_count : (primesBelow 30).length = 10 := by native_decide
