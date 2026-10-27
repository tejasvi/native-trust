-- A "native_decide build": nothing here knows about NativeTrust.
def isPrime (n : Nat) : Bool := n ≥ 2 && (List.range (n - 2)).all fun i => n % (i + 2) != 0

def primesBelow (n : Nat) : List Nat := (List.range n).filter isPrime

theorem count_primes : (primesBelow 2000).length = 303 := by native_decide

theorem sorted_check : ((List.range 500).reverse.mergeSort).take 3 = [0, 1, 2] := by native_decide

/-- A lemma using a native_decide fact inside its proof. -/
theorem primes_nonempty : primesBelow 2000 ≠ [] := by
  intro h
  have := count_primes
  rw [h] at this
  simp at this

theorem combined : (primesBelow 2000).length = 303 ∧ primesBelow 2000 ≠ [] :=
  ⟨count_primes, primes_nonempty⟩
