import Mathlib.NumberTheory.LucasPrimality

/-!
# Kernel-checked Pratt primality certificates

`Nat.Prime p` for large concrete `p` from a Pratt (Lucas) certificate. The side conditions are
`Bool` computations on `Nat` that the kernel evaluates with its GMP-accelerated `Nat` operations
(`+ - * / % ^`, `Nat.beq`, `Nat.ble`): no `native_decide`, no `Lean.ofReduceBool`, no axioms beyond
`propext`, `Classical.choice` and `Quot.sound`.

* `powMod b e m`: binary exponentiation by structural recursion on a fuel argument. The fuel is
  `e` itself and the loop stops as soon as the exponent reaches `0`, so it runs `log₂ e + 1`
  steps. `powMod_eq : powMod b e m = b ^ e % m` for every `m`.
* `pratt_step`: the Lucas test (`lucas_primality`) with the prime factorization of `p - 1` given as
  a list of `(q, e)` pairs.
* `checkStep`, `checkStep_sound`: the same side conditions, except the primality of the factors,
  as one `Bool`.
* `Cert`, `checkCert`, `checkTop`, `prime_of_checkTop`: a whole certificate tree as a flat list of
  nodes `(p, a, fs)`. Each factor `q` of a node is `2` or the prime of an earlier node, so one
  `decide +kernel` proves the primality of every node.

Usage:
```
def myCert : PrattCert.Cert := [(3, 2, [(2, 1)]), (7, 3, [(2, 1), (3, 1)])]
theorem prime_seven : Nat.Prime 7 := PrattCert.prime_of_checkTop (c := myCert) (by decide +kernel)
```
-/

namespace PrattCert

/-! ### Modular exponentiation -/

/-- Square-and-multiply loop: `powModAux fuel b e m r ≡ r * b ^ e [MOD m]` when `e ≤ fuel`. -/
def powModAux (fuel b e m r : Nat) : Nat :=
  match fuel with
  | 0 => r
  | fuel + 1 =>
    if e = 0 then r
    else powModAux fuel (b * b % m) (e / 2) m (if e % 2 = 1 then r * b % m else r)
termination_by structural fuel

/-- Modular exponentiation `b ^ e % m` by repeated squaring (fuel `e`, `log₂ e + 1` steps). -/
def powMod (b e m : Nat) : Nat := powModAux e b e m 1 % m

theorem powModAux_mod (fuel b e m r : Nat) (h : e ≤ fuel) :
    powModAux fuel b e m r % m = r * b ^ e % m := by
  induction fuel generalizing b e r with
  | zero =>
    obtain rfl : e = 0 := by omega
    simp [powModAux]
  | succ n ih =>
    have key : r * b ^ e = r * b ^ (e % 2) * (b * b) ^ (e / 2) := by
      conv_lhs => rw [← Nat.div_add_mod e 2]
      rw [pow_add, pow_mul, sq]
      ring
    rw [powModAux]
    split_ifs with he h2
    · subst he; simp
    · rw [ih _ _ _ (by omega), key, h2, pow_one]
      exact (Nat.mod_modEq _ _).mul ((Nat.mod_modEq _ _).pow _)
    · rw [ih _ _ _ (by omega), key, show e % 2 = 0 by omega, pow_zero, mul_one]
      exact (Nat.ModEq.refl r).mul ((Nat.mod_modEq _ _).pow _)

theorem powMod_eq (b e m : Nat) : powMod b e m = b ^ e % m := by
  rw [powMod, powModAux_mod _ _ _ _ _ le_rfl, one_mul]

/-! ### Factor lists -/

/-- `∏ q ^ e` over a factor list, by plain structural recursion. -/
def prodPow : List (Nat × Nat) → Nat
  | [] => 1
  | qe :: fs => qe.1 ^ qe.2 * prodPow fs

theorem prodPow_eq (fs : List (Nat × Nat)) :
    prodPow fs = (fs.map fun qe => qe.1 ^ qe.2).prod := by
  induction fs with
  | nil => rfl
  | cons qe fs ih => simp [prodPow, ih]

/-- A prime dividing a product of powers of listed primes is one of the listed primes. -/
theorem exists_mem_of_prime_dvd_prod {q : Nat} (hq : q.Prime) :
    ∀ fs : List (Nat × Nat), (∀ qe ∈ fs, qe.1.Prime) →
      q ∣ (fs.map fun qe => qe.1 ^ qe.2).prod → ∃ qe ∈ fs, qe.1 = q
  | [], _, h => by
    simp only [List.map_nil, List.prod_nil, Nat.dvd_one] at h
    exact absurd h hq.ne_one
  | qe :: fs, hfs, h => by
    rw [List.map_cons, List.prod_cons] at h
    rcases hq.dvd_mul.1 h with h1 | h1
    · exact ⟨qe, List.mem_cons.2 (Or.inl rfl),
        ((Nat.prime_dvd_prime_iff_eq hq (hfs qe (List.mem_cons.2 (Or.inl rfl)))).1
          (hq.dvd_of_dvd_pow h1)).symm⟩
    · obtain ⟨qe', hmem, heq⟩ := exists_mem_of_prime_dvd_prod hq fs
        (fun x hx => hfs x (List.mem_cons.2 (Or.inr hx))) h1
      exact ⟨qe', List.mem_cons.2 (Or.inr hmem), heq⟩

/-! ### The Lucas step -/

/-- Pratt step: if `p - 1 = ∏ q ^ e` over the list `fs` of primes, `a ^ (p - 1) ≡ 1 [MOD p]` and
`a ^ ((p - 1) / q) ≢ 1 [MOD p]` for every listed `q`, then `p` is prime. -/
theorem pratt_step (p a : Nat) (fs : List (Nat × Nat))
    (hprod : p - 1 = (fs.map fun qe => qe.1 ^ qe.2).prod)
    (hfs : ∀ qe ∈ fs, qe.1.Prime) (hp : 2 ≤ p)
    (ha : powMod a (p - 1) p = 1)
    (hd : ∀ qe ∈ fs, powMod a ((p - 1) / qe.1) p ≠ 1) : p.Prime := by
  have h1 : 1 % p = 1 := Nat.mod_eq_of_lt (by omega)
  have key : ∀ k : Nat, (a : ZMod p) ^ k = 1 ↔ powMod a k p = 1 := by
    intro k
    rw [powMod_eq, ← Nat.cast_pow, ← Nat.cast_one, ZMod.natCast_eq_natCast_iff', h1]
  refine lucas_primality p (a : ZMod p) ((key _).2 ha) ?_
  intro q hq hdvd hpow
  obtain ⟨qe, hmem, rfl⟩ := exists_mem_of_prime_dvd_prod hq fs hfs (hprod ▸ hdvd)
  exact hd qe hmem ((key _).1 hpow)

/-! ### `Bool` checks -/

/-- Membership in a list of numbers, by `Nat.beq`. -/
def memNat (q : Nat) : List Nat → Bool
  | [] => false
  | x :: xs => Nat.beq q x || memNat q xs

theorem mem_of_memNat {q : Nat} : ∀ {l : List Nat}, memNat q l = true → q ∈ l
  | [], h => by simp [memNat] at h
  | x :: xs, h => by
    simp only [memNat, Bool.or_eq_true, Nat.beq_eq] at h
    rcases h with rfl | h
    · exact List.mem_cons.2 (Or.inl rfl)
    · exact List.mem_cons.2 (Or.inr (mem_of_memNat h))

/-- The side conditions of `pratt_step`, except the primality of the factors, as one `Bool`. -/
def checkStep (p a : Nat) (fs : List (Nat × Nat)) : Bool :=
  Nat.ble 2 p && Nat.beq (p - 1) (prodPow fs) && Nat.beq (powMod a (p - 1) p) 1 &&
    fs.all fun qe => !Nat.beq (powMod a ((p - 1) / qe.1) p) 1

theorem checkStep_sound {p a : Nat} {fs : List (Nat × Nat)} (h : checkStep p a fs = true)
    (hfs : ∀ qe ∈ fs, qe.1.Prime) : p.Prime := by
  simp only [checkStep, Bool.and_eq_true, Nat.ble_eq, Nat.beq_eq, List.all_eq_true] at h
  obtain ⟨⟨⟨hp, hprod⟩, ha⟩, hd⟩ := h
  refine pratt_step p a fs (hprod.trans (prodPow_eq fs)) hfs hp ha fun qe hqe heq => ?_
  have h' := hd qe hqe
  rw [heq] at h'
  exact absurd h' (by decide)

/-- A Pratt certificate: nodes `(p, a, fs)` with a prime `p`, a Lucas witness `a` and the prime
factorization `fs` of `p - 1` as `(q, e)` pairs. Every factor `q` of a node must be `2` or the
prime of an earlier node. -/
abbrev Cert := List (Nat × Nat × List (Nat × Nat))

/-- Checks the nodes in order; `known` holds the primes already established. -/
def checkCert : List Nat → Cert → Bool
  | _, [] => true
  | known, (p, a, fs) :: rest =>
    (checkStep p a fs && fs.all fun qe => Nat.beq qe.1 2 || memNat qe.1 known) &&
      checkCert (p :: known) rest

theorem checkCert_sound : ∀ (known : List Nat) (c : Cert), (∀ q ∈ known, q.Prime) →
    checkCert known c = true → ∀ x ∈ c, x.1.Prime
  | _, [], _, _ => by simp
  | known, (p, a, fs) :: rest, hk, h => by
    simp only [checkCert, Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, Nat.beq_eq] at h
    obtain ⟨⟨hstep, hfs⟩, hrest⟩ := h
    have hp : p.Prime := checkStep_sound hstep fun qe hqe => by
      rcases hfs qe hqe with h2 | hm
      · rw [h2]; exact Nat.prime_two
      · exact hk _ (mem_of_memNat hm)
    have ih := checkCert_sound (p :: known) rest (by
      intro q hq
      rcases List.mem_cons.1 hq with rfl | hq
      · exact hp
      · exact hk q hq) hrest
    intro x hx
    rcases List.mem_cons.1 hx with rfl | hx
    · exact hp
    · exact ih x hx

/-- `p` is the prime of a node of the certificate `c`, and `c` is valid. -/
def checkTop (p : Nat) (c : Cert) : Bool :=
  memNat p (c.map (·.1)) && checkCert [] c

theorem prime_of_checkTop {p : Nat} {c : Cert} (h : checkTop p c = true) : p.Prime := by
  simp only [checkTop, Bool.and_eq_true] at h
  obtain ⟨hm, hc⟩ := h
  obtain ⟨x, hx, rfl⟩ := List.mem_map.1 (mem_of_memNat hm)
  exact checkCert_sound [] c (by simp) hc x hx

end PrattCert
