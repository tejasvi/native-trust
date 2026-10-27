module

public import BVS.Sound.Circuits

@[expose] public section
/-!
# Soundness of the bit-blaster: the bit-list functions compute `BitVec` operations
-/
namespace BVS
open Std.Tactic.BVDecide

/-- Bits `i, …, i+n-1` of `x`. -/
def bitsFrom {w : Nat} (x : BitVec w) (i n : Nat) : List Bool := (List.range' i n).map x.getLsbD

/-- The bits of `x`, least significant first. -/
def bitsOf {w : Nat} (x : BitVec w) : List Bool := bitsFrom x 0 w

theorem bitsFrom_zero {w : Nat} (x : BitVec w) (i : Nat) : bitsFrom x i 0 = [] := rfl

theorem bitsFrom_succ {w : Nat} (x : BitVec w) (i n : Nat) :
    bitsFrom x i (n + 1) = x.getLsbD i :: bitsFrom x (i + 1) n := by
  simp [bitsFrom, List.range'_succ]

theorem length_bitsFrom {w : Nat} (x : BitVec w) (i n : Nat) : (bitsFrom x i n).length = n := by
  simp [bitsFrom]

theorem length_bitsOf {w : Nat} (x : BitVec w) : (bitsOf x).length = w := length_bitsFrom x 0 w

theorem getElem_bitsFrom {w : Nat} (x : BitVec w) (i n j : Nat) (h : j < (bitsFrom x i n).length) :
    (bitsFrom x i n)[j] = x.getLsbD (i + j) := by
  simp [bitsFrom]

theorem getD_bitsOf {w : Nat} (x : BitVec w) (j : Nat) : (bitsOf x).getD j false = x.getLsbD j := by
  rw [List.getD_eq_getElem?_getD]
  by_cases h : j < w
  · rw [List.getElem?_eq_getElem (by simpa [length_bitsOf] using h)]
    simp [bitsOf, getElem_bitsFrom]
  · rw [List.getElem?_eq_none (by simp [length_bitsOf]; omega)]
    simp [BitVec.getLsbD_of_ge x j (by omega)]

theorem bitsOf_ext {w : Nat} (x : BitVec w) (l : List Bool) (hl : l.length = w)
    (h : ∀ j (hj : j < w), l[j]'(by omega) = x.getLsbD j) : l = bitsOf x := by
  apply List.ext_getElem
  · rw [hl, length_bitsOf]
  · intro j h1 h2
    rw [h j (by omega)]
    simp [bitsOf, getElem_bitsFrom]

theorem bitsOf_ext' {w : Nat} (x : BitVec w) (l : List Bool) (hl : l.length = w)
    (h : ∀ j, j < w → l.getD j false = x.getLsbD j) : l = bitsOf x := by
  apply bitsOf_ext x l hl
  intro j hj
  rw [← h j hj, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem]; rfl

theorem takeDL_getD (n : Nat) (l : List Bool) (j : Nat) :
    (takeDL n l).getD j false = if j < n then l.getD j false else false := by
  induction n generalizing l j with
  | zero => simp [takeDL]
  | succ n ih =>
    cases l with
    | nil => cases j with
      | zero => simp [takeDL]
      | succ j => simp only [takeDL, List.getD_cons_succ, ih]; simp
    | cons b l => cases j with
      | zero => simp [takeDL]
      | succ j => simp only [takeDL, List.getD_cons_succ, ih]; simp

theorem bitsOf_cast {w w' : Nat} (h : w = w') (x : BitVec w) : bitsOf (h ▸ x) = bitsOf x := by
  subst h; rfl

/-! ## Bitwise operations -/

theorem zipWith_bitsFrom (f : Bool → Bool → Bool) {w : Nat} (x y : BitVec w) (i n : Nat) :
    List.zipWith f (bitsFrom x i n) (bitsFrom y i n) =
      (List.range' i n).map (fun j => f (x.getLsbD j) (y.getLsbD j)) := by
  induction n generalizing i with
  | zero => rfl
  | succ n ih => simp [bitsFrom_succ, ih, List.range'_succ]

theorem bitsOf_zipWith (f : Bool → Bool → Bool) {w : Nat} (x y z : BitVec w)
    (h : ∀ j, j < w → z.getLsbD j = f (x.getLsbD j) (y.getLsbD j)) :
    List.zipWith f (bitsOf x) (bitsOf y) = bitsOf z := by
  rw [bitsOf, bitsOf, zipWith_bitsFrom, bitsOf, bitsFrom]
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range'] at hj
  rw [h j (by omega)]

theorem bitsOf_and {w : Nat} (x y : BitVec w) :
    List.zipWith (· && ·) (bitsOf x) (bitsOf y) = bitsOf (x &&& y) :=
  bitsOf_zipWith _ x y _ fun j _ => by simp

theorem bitsOf_or {w : Nat} (x y : BitVec w) :
    List.zipWith (· || ·) (bitsOf x) (bitsOf y) = bitsOf (x ||| y) :=
  bitsOf_zipWith _ x y _ fun j _ => by simp

theorem bitsOf_xor {w : Nat} (x y : BitVec w) :
    List.zipWith (· ^^ ·) (bitsOf x) (bitsOf y) = bitsOf (x ^^^ y) :=
  bitsOf_zipWith _ x y _ fun j _ => by simp

theorem bitsOf_not {w : Nat} (x : BitVec w) : (bitsOf x).map not = bitsOf (~~~x) := by
  rw [bitsOf, bitsOf, bitsFrom, bitsFrom, List.map_map]
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range'] at hj
  simp [show j < w by omega]

/-! ## Addition and comparison -/

theorem atLeastTwo_eq_majB (a b c : Bool) : Bool.atLeastTwo a b c = majB a b c := by
  cases a <;> cases b <;> cases c <;> rfl

theorem addL_bitsFrom {w : Nat} (x y : BitVec w) (c : Bool) : ∀ (n i : Nat), i + n ≤ w →
    addL (bitsFrom x i n) (bitsFrom y i n) (BitVec.carry i x y c) =
      (bitsFrom (x + y + BitVec.setWidth w (BitVec.ofBool c)) i n, BitVec.carry (i + n) x y c)
  | 0, i, _ => by simp [bitsFrom_zero, addL]
  | n + 1, i, h => by
    have hc : majB (x.getLsbD i) (y.getLsbD i) (BitVec.carry i x y c) = BitVec.carry (i + 1) x y c := by
      rw [BitVec.carry_succ, atLeastTwo_eq_majB]
    simp only [bitsFrom_succ, addL, hc, addL_bitsFrom x y c n (i + 1) (by omega)]
    rw [BitVec.getLsbD_add_add_bool (by omega), show i + 1 + n = i + (n + 1) by omega]
    simp [Bool.xor_assoc]

theorem addL_bitsOf {w : Nat} (x y : BitVec w) (c : Bool) :
    addL (bitsOf x) (bitsOf y) c = (bitsOf (x + y + BitVec.setWidth w (BitVec.ofBool c)), BitVec.carry w x y c) := by
  have := addL_bitsFrom x y c w 0 (by omega)
  simp only [BitVec.carry_zero, Nat.zero_add] at this
  exact this

theorem addL_bitsOf_false {w : Nat} (x y : BitVec w) : (addL (bitsOf x) (bitsOf y) false).1 = bitsOf (x + y) := by
  rw [addL_bitsOf]
  show bitsOf _ = bitsOf _
  congr 1
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp

theorem ult_bitsOf {w : Nat} (x y : BitVec w) :
    (!(addL (bitsOf x) ((bitsOf y).map not) true).2) = x.ult y := by
  rw [bitsOf_not, addL_bitsOf, BitVec.ult_eq_not_carry]

theorem allL_zipWith_beq {w : Nat} (x y : BitVec w) : ∀ (n i : Nat),
    allL (List.zipWith (· == ·) (bitsFrom x i n) (bitsFrom y i n)) = true ↔
      ∀ j, i ≤ j → j < i + n → x.getLsbD j = y.getLsbD j
  | 0, i => by simp only [bitsFrom_zero, List.zipWith_nil_left, allL, true_iff]; intro j h1 h2; omega
  | n + 1, i => by
    simp only [bitsFrom_succ, List.zipWith_cons_cons, allL, Bool.and_eq_true, beq_iff_eq,
      allL_zipWith_beq x y n (i + 1)]
    constructor
    · rintro ⟨h0, h1⟩ j hj1 hj2
      by_cases hj : j = i
      · subst hj; exact h0
      · exact h1 j (by omega) (by omega)
    · intro h
      exact ⟨h i (by omega) (by omega), fun j hj1 hj2 => h j (by omega) (by omega)⟩

theorem eq_bitsOf {w : Nat} (x y : BitVec w) :
    allL (List.zipWith (· == ·) (bitsOf x) (bitsOf y)) = (x == y) := by
  apply Bool.eq_iff_iff.mpr
  rw [bitsOf, bitsOf, allL_zipWith_beq, beq_iff_eq]
  constructor
  · intro h; apply BitVec.eq_of_getLsbD_eq; intro j hj; exact h j (Nat.zero_le _) (by omega)
  · rintro rfl j _ _; rfl

/-! ## Constants, extraction, concatenation -/

theorem map_constBits (env : Nat → Bool) (h0 : env 0 = false) :
    ∀ (n v i : Nat), (constBits n v).map (lv env) = (List.range' i n).map (fun j => v.testBit (j - i))
  | 0, v, i => rfl
  | n + 1, v, i => by
    simp only [constBits, List.map_cons, nat_beq_eq, cond_decide]
    rw [map_constBits env h0 n (v / 2) (i + 1), List.range'_succ]
    simp only [List.map_cons, Nat.sub_self]
    congr 1
    · split
      · rw [lv_zero h0, Nat.testBit_zero]; simp [*]
      · rw [lv_one h0, Nat.testBit_zero]; simp; omega
    · apply List.map_congr_left
      intro j hj
      simp only [List.mem_range'] at hj
      rw [show j - i = (j - (i + 1)) + 1 by omega, Nat.testBit_succ]

theorem bitsOf_const {w : Nat} (env : Nat → Bool) (h0 : env 0 = false) (val : BitVec w) :
    (constBits w val.toNat).map (lv env) = bitsOf val := by
  rw [map_constBits env h0 w val.toNat 0, bitsOf, bitsFrom]
  apply List.map_congr_left
  intro j _
  rfl

theorem takeDL_getElem (n : Nat) (l : List Bool) (j : Nat) (h : j < (takeDL n l).length) :
    (takeDL n l)[j] = l.getD j false := by
  induction n generalizing l j with
  | zero => simp [takeDL] at h
  | succ n ih =>
    cases l with
    | nil =>
      cases j with
      | zero => simp [takeDL]
      | succ j => simp only [takeDL, List.getElem_cons_succ]; rw [ih]; simp
    | cons b l =>
      cases j with
      | zero => simp [takeDL]
      | succ j => simp only [takeDL, List.getElem_cons_succ]; rw [ih]; simp

theorem bitsOf_extract {w : Nat} (x : BitVec w) (start len : Nat) :
    takeDL len ((bitsOf x).drop start) = bitsOf (BitVec.extractLsb' start len x) := by
  apply bitsOf_ext _ _ (length_takeDL _ _)
  intro j hj
  rw [takeDL_getElem]
  simp only [BitVec.getLsbD_extractLsb', hj, decide_true, Bool.true_and]
  rw [List.getD_eq_getElem?_getD, List.getElem?_drop, ← List.getD_eq_getElem?_getD, getD_bitsOf]

theorem bitsOf_append {l r : Nat} (x : BitVec l) (y : BitVec r) :
    bitsOf y ++ bitsOf x = bitsOf (x ++ y) := by
  apply bitsOf_ext _ _ (by simp [length_bitsOf]; omega)
  intro j hj
  rw [BitVec.getLsbD_append]
  by_cases h : j < r
  · rw [List.getElem_append_left (by simpa [length_bitsOf] using h)]
    simp [bitsOf, getElem_bitsFrom, h]
  · rw [List.getElem_append_right (by simp [length_bitsOf]; omega)]
    simp [bitsOf, getElem_bitsFrom, h, length_bitsFrom]
/-! ## Multiplication -/

theorem bitsOf_zero (w : Nat) : bitsOf (0#w) = List.replicate w false := by
  symm; apply bitsOf_ext _ _ (by simp)
  intro j hj; simp

theorem shlL_bitsOf {w : Nat} (x : BitVec w) (i : Nat) : shlL (bitsOf x) i = bitsOf (x <<< i) := by
  apply bitsOf_ext' _ _ (by simp [shlL, length_takeDL, length_bitsOf])
  intro j hj
  simp only [shlL, length_bitsOf, takeDL_getD, hj, if_true, BitVec.getLsbD_shiftLeft, decide_true,
    Bool.true_and]
  rw [List.getD_eq_getElem?_getD]
  by_cases h : j < i
  · rw [List.getElem?_append_left (by simpa using h)]; simp [h]
  · rw [List.getElem?_append_right (by simp; omega)]
    simp only [List.length_replicate, h, decide_false, Bool.not_false, Bool.true_and]
    rw [← List.getD_eq_getElem?_getD, getD_bitsOf]

/-- The partial products: the first `k` bits of `y`. -/
def partProd {w : Nat} (x y : BitVec w) : Nat → BitVec w
  | 0 => 0
  | k + 1 => partProd x y k + (if y.getLsbD k then x <<< k else 0)

theorem mulRec_eq_partProd {w : Nat} (x y : BitVec w) : ∀ s, BitVec.mulRec x y s = partProd x y (s + 1)
  | 0 => by
    rw [BitVec.mulRec_zero_eq]; simp only [partProd, BitVec.shiftLeft_zero]
    cases y.getLsbD 0 <;> simp
  | s + 1 => by rw [BitVec.mulRec_succ_eq, mulRec_eq_partProd x y s]; rfl

theorem mul_eq_partProd {w : Nat} (x y : BitVec w) : x * y = partProd x y w := by
  rw [BitVec.mul_eq_mulRec, mulRec_eq_partProd]
  simp [partProd, BitVec.getLsbD_of_ge y w (Nat.le_refl _)]

theorem mulL_bits {w : Nat} (x y : BitVec w) : ∀ (n i : Nat),
    mulL (bitsOf x) (bitsFrom y i n) i (bitsOf (partProd x y i)) = bitsOf (partProd x y (i + n))
  | 0, i => rfl
  | n + 1, i => by
    rw [bitsFrom_succ, mulL, shlL_bitsOf]
    have : (if y.getLsbD i then (addL (bitsOf (partProd x y i)) (bitsOf (x <<< i)) false).1
        else bitsOf (partProd x y i)) = bitsOf (partProd x y (i + 1)) := by
      rw [addL_bitsOf_false]
      cases h : y.getLsbD i <;> simp [partProd, h]
    rw [this, mulL_bits x y n (i + 1), show i + 1 + n = i + (n + 1) by omega]

theorem mul_bitsOf {w : Nat} (x y : BitVec w) :
    mulL (bitsOf x) (bitsOf y) 0 (List.replicate w false) = bitsOf (x * y) := by
  have := mulL_bits x y w 0
  rw [Nat.zero_add, ← mul_eq_partProd] at this
  rw [← this, ← bitsOf_zero]; rfl

/-! ## Division -/

theorem shiftConcatL_bitsOf {w : Nat} (x : BitVec w) (b : Bool) :
    shiftConcatL (bitsOf x) b = bitsOf (x.shiftConcat b) := by
  apply bitsOf_ext' _ _ (by simp [shiftConcatL, length_takeDL, length_bitsOf])
  intro j hj
  simp only [shiftConcatL, length_bitsOf, takeDL_getD, hj, if_true, BitVec.getLsbD_shiftConcat,
    decide_true, Bool.true_and]
  cases j with
  | zero => simp
  | succ j => simp only [List.getD_cons_succ, getD_bitsOf]; simp

theorem setWidth_ofBool_true (w : Nat) : BitVec.setWidth w (BitVec.ofBool true) = 1#w := by
  apply BitVec.eq_of_getLsbD_eq
  intro i hi
  simp only [BitVec.getLsbD_setWidth, BitVec.ofBool_true, BitVec.getLsbD_one, hi, decide_true,
    Bool.true_and]
  simp; omega

theorem sub_eq_add_not_add_one {w : Nat} (x y : BitVec w) :
    x + ~~~y + BitVec.setWidth w (BitVec.ofBool true) = x - y := by
  rw [setWidth_ofBool_true, BitVec.sub_eq_add_neg, BitVec.neg_eq_not_add, BitVec.add_assoc]

theorem sub_eq_add_not_add_one' {w : Nat} (x y : BitVec w) :
    x + ~~~y + BitVec.setWidth w 1#1 = x - y :=
  sub_eq_add_not_add_one x y

theorem divStepL_bits {w : Nat} (N D Q R : BitVec w) (wn wr : Nat) :
    divStepL (bitsOf N) (bitsOf D) wn (bitsOf Q) (bitsOf R) =
      (bitsOf (BitVec.divSubtractShift ⟨N, D⟩ ⟨wn, wr, Q, R⟩).q,
       bitsOf (BitVec.divSubtractShift ⟨N, D⟩ ⟨wn, wr, Q, R⟩).r) := by
  simp only [divStepL, getD_bitsOf, shiftConcatL_bitsOf, bitsOf_not, addL_bitsOf]
  generalize hR : R.shiftConcat (N.getLsbD (wn - 1)) = R'
  have hc : BitVec.carry w R' (~~~D) true = !(decide (R' < D)) := by
    have := BitVec.ult_eq_not_carry R' D
    have e : R'.ult D = decide (R' < D) := by simp [BitVec.ult, BitVec.lt_def]
    rw [← e, this]; simp
  simp only [BitVec.divSubtractShift, hR, hc]
  by_cases h : R' < D
  · simp [h]
  · simp [h, sub_eq_add_not_add_one']

theorem divGoL_bits {w : Nat} (N D : BitVec w) : ∀ (k wn wr : Nat) (Q R : BitVec w),
    divGoL (bitsOf N) (bitsOf D) k wn (bitsOf Q) (bitsOf R) =
      (bitsOf (BitVec.divRec k ⟨N, D⟩ ⟨wn, wr, Q, R⟩).q, bitsOf (BitVec.divRec k ⟨N, D⟩ ⟨wn, wr, Q, R⟩).r)
  | 0, _, _, _, _ => rfl
  | k + 1, wn, wr, Q, R => by
    rw [divGoL, divStepL_bits N D Q R wn wr, BitVec.divRec_succ]
    have e : BitVec.divSubtractShift ⟨N, D⟩ ⟨wn, wr, Q, R⟩ =
        ⟨wn - 1, wr + 1, (BitVec.divSubtractShift ⟨N, D⟩ ⟨wn, wr, Q, R⟩).q,
          (BitVec.divSubtractShift ⟨N, D⟩ ⟨wn, wr, Q, R⟩).r⟩ := by
      simp only [BitVec.divSubtractShift]; split <;> rfl
    rw [divGoL_bits N D k (wn - 1) (wr + 1), ← e]

theorem udiv_bitsOf {w : Nat} (N D : BitVec w) :
    (if allL (List.zipWith (· == ·) (bitsOf D) (List.replicate w false)) then List.replicate w false
     else (divGoL (bitsOf N) (bitsOf D) w w (List.replicate w false) (List.replicate w false)).1) =
      bitsOf (N / D) := by
  rw [← bitsOf_zero, eq_bitsOf, divGoL_bits N D w w 0]
  by_cases h : D = 0#w
  · simp [h, BitVec.udiv_zero]
  · have hd : 0#w < D := by
      rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat, Nat.zero_mod]
      have : D.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simp [h']))
      omega
    simp only [h, beq_iff_eq, if_false, decide_false]
    rw [BitVec.udiv_eq_divRec hd]; rfl

theorem umod_bitsOf {w : Nat} (N D : BitVec w) :
    (if allL (List.zipWith (· == ·) (bitsOf D) (List.replicate w false)) then bitsOf N
     else (divGoL (bitsOf N) (bitsOf D) w w (List.replicate w false) (List.replicate w false)).2) =
      bitsOf (N % D) := by
  rw [← bitsOf_zero, eq_bitsOf, divGoL_bits N D w w 0]
  by_cases h : D = 0#w
  · simp [h, BitVec.umod_zero]
  · have hd : 0#w < D := by
      rw [BitVec.lt_def]; simp only [BitVec.toNat_ofNat, Nat.zero_mod]
      have : D.toNat ≠ 0 := fun h' => h (BitVec.eq_of_toNat_eq (by simp [h']))
      omega
    simp only [h, beq_iff_eq, if_false, decide_false]
    rw [BitVec.umod_eq_divRec hd]; rfl

end BVS
