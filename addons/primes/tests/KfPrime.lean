import Mathlib.Data.Nat.Prime.Basic

/-! Stand-in for a field library: the primality instance by `native_decide` (as in
Verified-zkEVM/clean), and a downstream fact that depends on it. -/

def pBabybear : ℕ := 15 * 2 ^ 27 + 1

instance babybearPrime : Fact (Nat.Prime pBabybear) := by native_decide

theorem pBabybear_prime : Nat.Prime pBabybear := Fact.out

theorem pBabybear_pos : 0 < pBabybear := (Fact.out : Nat.Prime pBabybear).pos
