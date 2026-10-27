import BVS.Sound.Bits
/-!
# Soundness of the bit-blaster: shifts, rotations, replication
-/
namespace BVS
open Std.Tactic.BVDecide

variable {av : Nat → Nat → Bool}

/-! ## Bool-list semantics -/

def takeFL (f : Bool) : Nat → List Bool → List Bool
  | 0, _ => []
  | n + 1, [] => f :: takeFL f n []
  | n + 1, b :: bs => b :: takeFL f n bs

def shrL (as : List Bool) (k : Nat) : List Bool := takeDL as.length (as.drop k)

def sarL (as : List Bool) (k : Nat) : List Bool := takeFL (as.getD (as.length - 1) false) as.length (as.drop k)

def barrelL (shL : List Bool → Nat → List Bool) : List Bool → List Bool → Nat → List Bool
  | acc, [], _ => acc
  | acc, y :: ys, i => barrelL shL (if y then shL acc (2 ^ i) else acc) ys (i + 1)

def rotlL (as : List Bool) (r : Nat) : List Bool :=
  as.drop (as.length - r % as.length) ++ as.take (as.length - r % as.length)

def rotrL (as : List Bool) (r : Nat) : List Bool :=
  as.drop (r % as.length) ++ as.take (r % as.length)

/-! ## Circuits -/

theorem length_takeF (f n : Nat) (l : List Nat) : (takeF f n l).length = n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [takeF, ih]

theorem length_takeFL (f : Bool) (n : Nat) (l : List Bool) : (takeFL f n l).length = n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [takeFL, ih]

theorem map_takeF (env : Nat → Bool) (f : Nat) : ∀ (n : Nat) (l : List Nat),
    (takeF f n l).map (lv env) = takeFL (lv env f) n (l.map (lv env))
  | 0, _ => rfl
  | n + 1, [] => by simp [takeF, takeFL, map_takeF env f n []]
  | n + 1, x :: xs => by simp [takeF, takeFL, map_takeF env f n xs]

theorem takeDL_replicate_false (n k : Nat) (l : List Bool) (h : n ≤ k) :
    takeDL n (List.replicate k false ++ l) = List.replicate n false := by
  induction n generalizing k with
  | zero => rfl
  | succ n ih =>
    cases k with
    | zero => omega
    | succ k => simp [List.replicate_succ, takeDL, ih k (by omega)]

theorem length_shlC (xs : List Nat) (k : Nat) : (shlC xs k).length = xs.length := by
  simp only [shlC, nat_ble_eq, cond_decide]
  split
  · exact length_zeros _
  · exact length_shl xs k

theorem map_shlC (env : Nat → Bool) (h : env 0 = false) (xs : List Nat) (k : Nat) :
    (shlC xs k).map (lv env) = shlL (xs.map (lv env)) k := by
  simp only [shlC, nat_ble_eq, cond_decide]
  split
  · rw [map_zeros env h, shlL, List.length_map, takeDL_replicate_false _ _ _ (by assumption)]
  · exact map_shl env h xs k

theorem length_shrC (xs : List Nat) (k : Nat) : (shrC xs k).length = xs.length := by
  simp [shrC, length_takeD]

theorem map_shrC (env : Nat → Bool) (h : env 0 = false) (xs : List Nat) (k : Nat) :
    (shrC xs k).map (lv env) = shrL (xs.map (lv env)) k := by
  simp [shrC, shrL, map_takeD env h, List.map_drop]

theorem length_sarC (xs : List Nat) (k : Nat) : (sarC xs k).length = xs.length := by
  simp [sarC, length_takeF]

theorem map_sarC (env : Nat → Bool) (h : env 0 = false) (xs : List Nat) (k : Nat) :
    (sarC xs k).map (lv env) = sarL (xs.map (lv env)) k := by
  simp only [sarC, sarL, map_takeF, List.map_drop, List.length_map, getD_map_lv env h]

theorem barrel_spec (sh : List Nat → Nat → List Nat) (shL : List Bool → Nat → List Bool)
    (hlen : ∀ xs k, (sh xs k).length = xs.length)
    (hsem : ∀ (env : Nat → Bool), env 0 = false → ∀ xs k, (sh xs k).map (lv env) = shL (xs.map (lv env)) k) :
    ∀ (ys : List Nat) (st : St) (acc : List Nat) (i : Nat),
      Spec av st (barrel sh st acc ys i)
        (fun env r => r.map (lv env) = barrelL shL (acc.map (lv env)) (ys.map (lv env)) i)
  | [], st, acc, i => Spec.ret fun _ _ => rfl
  | y :: ys, st, acc, i => by
    unfold barrel
    rcases h1 : muxV st y (sh acc (2 ^ i)) acc with ⟨st1, acc'⟩
    have s1 := h1 ▸ muxV_spec (av := av) st y (sh acc (2 ^ i)) acc
    dsimp only
    refine Spec.bind s1 ((barrel_spec sh shL hlen hsem ys st1 acc' (i + 1)).weaken fun env r g H H1 => ?_)
    rw [H, H1, zipWith_mux (by rw [List.length_map, List.length_map, hlen]), hsem env g.1]
    simp only [List.map_cons, barrelL]

theorem map_rotl (f : Nat → Bool) (xs : List Nat) (r : Nat) : (rotl xs r).map f = rotlL (xs.map f) r := by
  simp [rotl, rotlL, List.map_drop, List.map_take]

theorem map_rotr (f : Nat → Bool) (xs : List Nat) (r : Nat) : (rotr xs r).map f = rotrL (xs.map f) r := by
  simp [rotr, rotrL, List.map_drop, List.map_take]

/-! ## The bit lists compute the `BitVec` operations -/

theorem shrL_bitsOf {w : Nat} (x : BitVec w) (k : Nat) : shrL (bitsOf x) k = bitsOf (x >>> k) := by
  apply bitsOf_ext' _ _ (by simp [shrL, length_takeDL, length_bitsOf])
  intro j hj
  simp only [shrL, length_bitsOf, takeDL_getD, hj, if_true, BitVec.getLsbD_ushiftRight]
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, getD_bitsOf]

theorem takeFL_getD (f : Bool) (n : Nat) (l : List Bool) (j : Nat) :
    (takeFL f n l).getD j false = if j < n then l.getD j f else false := by
  induction n generalizing l j with
  | zero => simp [takeFL]
  | succ n ih =>
    cases l with
    | nil => cases j with
      | zero => simp [takeFL]
      | succ j => simp only [takeFL, List.getD_cons_succ, ih]; simp
    | cons b l => cases j with
      | zero => simp [takeFL]
      | succ j => simp only [takeFL, List.getD_cons_succ, ih]; simp

theorem sarL_bitsOf {w : Nat} (x : BitVec w) (k : Nat) : sarL (bitsOf x) k = bitsOf (x.sshiftRight k) := by
  apply bitsOf_ext' _ _ (by simp [sarL, length_takeFL, length_bitsOf])
  intro j hj
  simp only [sarL, length_bitsOf, takeFL_getD, hj, if_true, BitVec.getLsbD_sshiftRight,
    show ¬ w ≤ j by omega, decide_false, Bool.not_false, Bool.true_and, getD_bitsOf]
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop]
  by_cases hk : k + j < w
  · rw [if_pos hk, List.getElem?_eq_getElem (by simp [length_bitsOf]; omega)]
    simp [bitsOf, getElem_bitsFrom]
  · rw [if_neg hk, List.getElem?_eq_none (by simp [length_bitsOf]; omega), BitVec.msb_eq_getLsbD_last]
    rfl

theorem mod_two_pow_succ' (y i : Nat) : y % 2 ^ (i + 1) = y % 2 ^ i + (if y.testBit i then 2 ^ i else 0) := by
  rw [Nat.mod_pow_succ]
  congr 1
  rw [Nat.testBit_eq_decide_div_mod_eq]
  have : y / 2 ^ i % 2 < 2 := Nat.mod_lt _ (by omega)
  by_cases h : y / 2 ^ i % 2 = 1
  · simp [h]
  · have h0 : y / 2 ^ i % 2 = 0 := by omega
    simp [h0]

/-- A barrel shifter computes the shift by the whole distance, for any shift family `S` with
`S (a + b)` the shift of `S a` by `b`. -/
theorem barrelL_bits {w₁ w₂ : Nat} (S : Nat → BitVec w₁) (shL : List Bool → Nat → List Bool)
    (hS : ∀ a k, shL (bitsOf (S a)) k = bitsOf (S (a + k))) (y : BitVec w₂) :
    ∀ (n i : Nat), i + n = w₂ →
      barrelL shL (bitsOf (S (y.toNat % 2 ^ i))) (bitsFrom y i n) i = bitsOf (S (y.toNat % 2 ^ (i + n)))
  | 0, i, _ => by simp [bitsFrom_zero, barrelL]
  | n + 1, i, h => by
    rw [bitsFrom_succ]
    simp only [barrelL]
    have : (if y.getLsbD i then shL (bitsOf (S (y.toNat % 2 ^ i))) (2 ^ i) else bitsOf (S (y.toNat % 2 ^ i))) =
        bitsOf (S (y.toNat % 2 ^ (i + 1))) := by
      rw [mod_two_pow_succ']
      simp only [BitVec.getLsbD]
      by_cases hb : y.toNat.testBit i = true
      · simp [hb, hS]
      · simp [hb]
    rw [this, barrelL_bits S shL hS y n (i + 1) (by omega), show i + 1 + n = i + (n + 1) by omega]

theorem barrelL_bitsOf {w₁ w₂ : Nat} (S : Nat → BitVec w₁) (shL : List Bool → Nat → List Bool)
    (hS : ∀ a k, shL (bitsOf (S a)) k = bitsOf (S (a + k))) (y : BitVec w₂) :
    barrelL shL (bitsOf (S 0)) (bitsOf y) 0 = bitsOf (S y.toNat) := by
  have := barrelL_bits S shL hS y w₂ 0 (by omega)
  simp only [Nat.pow_zero, Nat.mod_one, Nat.zero_add] at this
  rw [Nat.mod_eq_of_lt y.isLt] at this
  exact this

theorem rotlL_bitsOf {w : Nat} (x : BitVec w) (r : Nat) : rotlL (bitsOf x) r = bitsOf (x.rotateLeft r) := by
  apply bitsOf_ext' _ _ (by simp [rotlL, length_bitsOf]; try omega)
  intro j hj
  rw [BitVec.getLsbD_rotateLeft]
  have hw : 0 < w := by omega
  have hr : r % w < w := Nat.mod_lt _ hw
  simp only [rotlL, length_bitsOf]
  rw [List.getD_eq_getElem?_getD]
  by_cases hj' : j < r % w
  · rw [List.getElem?_append_left (by simp [length_bitsOf]; omega), List.getElem?_drop,
      ← List.getD_eq_getElem?_getD, getD_bitsOf]
    simp [hj']
    first | done | (congr 1; omega)
  · rw [List.getElem?_append_right (by simp [length_bitsOf]; omega), List.getElem?_take]
    simp only [List.length_drop, length_bitsOf]
    rw [if_pos (by omega), ← List.getD_eq_getElem?_getD, getD_bitsOf]
    simp [hj', hj]
    first | done | (congr 1; omega)

theorem rotrL_bitsOf {w : Nat} (x : BitVec w) (r : Nat) : rotrL (bitsOf x) r = bitsOf (x.rotateRight r) := by
  apply bitsOf_ext' _ _ (by simp [rotrL, length_bitsOf]; try omega)
  intro j hj
  rw [BitVec.getLsbD_rotateRight]
  have hw : 0 < w := by omega
  have hr : r % w < w := Nat.mod_lt _ hw
  simp only [rotrL, length_bitsOf]
  rw [List.getD_eq_getElem?_getD]
  by_cases hj' : j < w - r % w
  · rw [List.getElem?_append_left (by simp [length_bitsOf]; omega), List.getElem?_drop,
      ← List.getD_eq_getElem?_getD, getD_bitsOf]
    simp [hj']
  · rw [List.getElem?_append_right (by simp [length_bitsOf]; omega), List.getElem?_take]
    simp only [List.length_drop, length_bitsOf]
    rw [if_pos (by omega), ← List.getD_eq_getElem?_getD, getD_bitsOf]
    simp [hj', hj]
    first | done | (congr 1; omega)

theorem getD_flatten_replicate (l : List Bool) (hl : 0 < l.length) : ∀ (n j : Nat),
    ((List.replicate n l).flatten).getD j false = (decide (j < l.length * n) && l.getD (j % l.length) false)
  | 0, j => by simp
  | n + 1, j => by
    rw [List.replicate_succ, List.flatten_cons, List.getD_eq_getElem?_getD]
    by_cases hj : j < l.length
    · rw [List.getElem?_append_left hj, ← List.getD_eq_getElem?_getD, Nat.mod_eq_of_lt hj]
      simp [show j < l.length * (n + 1) by rw [Nat.mul_succ]; omega]
    · rw [List.getElem?_append_right (by omega), ← List.getD_eq_getElem?_getD, getD_flatten_replicate l hl n]
      have hm : (j - l.length) % l.length = j % l.length := by
        have := Nat.add_mod_right (j - l.length) l.length
        rw [Nat.sub_add_cancel (by omega)] at this
        exact this.symm
      rw [hm]
      congr 1
      simp only [decide_eq_decide]
      rw [Nat.mul_succ]; omega

theorem replicate_bitsOf {w : Nat} (n : Nat) (X : BitVec w) :
    (List.replicate n (bitsOf X)).flatten = bitsOf (X.replicate n) := by
  rcases Nat.eq_zero_or_pos w with hw | hw
  · subst hw
    apply bitsOf_ext' _ _ (by simp [length_bitsOf])
    intro j hj; simp at hj
  · apply bitsOf_ext' _ _ (by simp [length_bitsOf, Nat.mul_comm])
    intro j hj
    rw [getD_flatten_replicate _ (by simpa [length_bitsOf] using hw), BitVec.getLsbD_replicate, length_bitsOf,
      getD_bitsOf]

end BVS
