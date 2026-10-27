/-- Number of `i < n` with `n % (i + 1) = 0` (the divisors of `n` for `n ≥ 1`). -/
def divCount (n : Nat) : Nat :=
  (List.range n).foldl (fun acc i => if n % (i + 1) == 0 then acc + 1 else acc) 0

/-- `∑_{n < N} divCount n`: about `N² / 2` steps, so plain kernel evaluation takes seconds for `N = 1500`. -/
def divSum (N : Nat) : Nat := (List.range N).foldl (fun acc n => acc + divCount n) 0
