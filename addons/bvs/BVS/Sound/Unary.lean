module

public import BVS.Sound.Shifts

@[expose] public section
/-!
# Soundness of the bit-blaster: unary operations (`reverse`, `clz`, `cpop` and the others)

`blastUn_spec`: the literals of `blastUn op st xs` evaluate to the bits of `op.eval x` when `xs`
evaluates to the bits of `x`.
-/
namespace BVS
open Std.Tactic.BVDecide

variable {av : Nat → Nat → Bool}

/-! ## Bits of constants and single bits -/

theorem getElem_bitsOf {w : Nat} (x : BitVec w) (i : Nat) (h : i < (bitsOf x).length) :
    (bitsOf x)[i] = x.getLsbD i := by
  simp [bitsOf, bitsFrom]

theorem lv_getD {w : Nat} {env : Nat → Bool} (h0 : env 0 = false) {xs : List Nat} {x : BitVec w}
    (H : xs.map (lv env) = bitsOf x) (i : Nat) : lv env (xs.getD i 0) = x.getLsbD i := by
  have hl : xs.length = w := by rw [← length_bitsOf x, ← H, List.length_map]
  by_cases hi : i < w
  · rw [getD_eq_get xs i (by omega)]
    have := congrArg (fun l => l[i]?) H
    simp only [List.getElem?_map, List.getElem?_eq_getElem (show i < xs.length by omega)] at this
    rw [List.getElem?_eq_getElem (show i < (bitsOf x).length by rw [length_bitsOf]; omega)] at this
    simp only [Option.map_some, Option.some.injEq] at this
    rw [this, getElem_bitsOf]
  · rw [show xs.getD i 0 = 0 by simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (show xs.length ≤ i by omega)],
      lv_zero h0, BitVec.getLsbD_of_ge x i (by omega)]

theorem map_constBits_ofNat (env : Nat → Bool) (h0 : env 0 = false) (w v : Nat) :
    (constBits w v).map (lv env) = bitsOf (BitVec.ofNat w v) := by
  rw [map_constBits env h0 w v 0, bitsOf, bitsFrom]
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range'] at hj
  show v.testBit (j - 0) = (BitVec.ofNat w v).getLsbD j
  rw [BitVec.getLsbD_ofNat, Nat.sub_zero]
  simp [show j < w by omega]

theorem zipWith_bif (c : Bool) : ∀ (as bs : List Bool), as.length = bs.length →
    List.zipWith (fun a b => bif c then a else b) as bs = bif c then as else bs
  | [], [], _ => by cases c <;> rfl
  | a :: as, b :: bs, h => by
    simp only [List.zipWith_cons_cons]
    rw [zipWith_bif c as bs (by simpa using h)]
    cases c <;> rfl
  | [], _ :: _, h => by simp at h
  | _ :: _, [], h => by simp at h

theorem bitsOf_ite {w : Nat} (c : Bool) (x y : BitVec w) :
    (bif c then bitsOf x else bitsOf y) = bitsOf (if c = true then x else y) := by
  cases c <;> rfl

/-! ## reverse -/

theorem bitsOf_reverse {w : Nat} (x : BitVec w) : bitsOf x.reverse = (bitsOf x).reverse := by
  apply List.ext_getElem
  · simp [length_bitsOf]
  · intro i h1 h2
    rw [getElem_bitsOf, List.getElem_reverse, getElem_bitsOf, BitVec.getLsbD_reverse, BitVec.getMsbD_eq_getLsbD]
    have hi : i < w := by rw [length_bitsOf] at h1; exact h1
    simp [hi, length_bitsOf]

/-! ## clz -/

theorem clzGo_spec (xs : List Nat) (w : Nat) (x : BitVec w) : ∀ (n : Nat) (st : St),
    Spec av st (clzGo xs w n st) (fun env r =>
      xs.map (lv env) = bitsOf x → r.map (lv env) = bitsOf (BitVec.clzAuxRec x n))
  | 0, st => by
    simp only [clzGo]
    exact (muxV_spec st _ _ _).weaken fun env r g H Hx => by
      rw [H, map_constBits_ofNat env g.1, map_constBits_ofNat env g.1, lv_getD g.1 Hx,
        zipWith_bif _ _ _ (by simp [length_bitsOf]), bitsOf_ite]
      rfl
  | n + 1, st => by
    simp only [clzGo]
    rcases h1 : clzGo xs w n st with ⟨st1, r1⟩
    have s1 := h1 ▸ clzGo_spec xs w x n st
    dsimp only
    exact Spec.bind s1 ((muxV_spec st1 _ _ _).weaken fun env r g H Hr Hx => by
      rw [H, map_constBits_ofNat env g.1, Hr Hx, lv_getD g.1 Hx,
        zipWith_bif _ _ _ (by simp [length_bitsOf]), bitsOf_ite]
      rfl)

theorem blastClz_spec (st : St) (xs : List Nat) {w : Nat} (x : BitVec w) :
    Spec av st (blastClz st xs) (fun env r => xs.map (lv env) = bitsOf x → r.map (lv env) = bitsOf x.clz) := by
  unfold blastClz
  by_cases hl : xs.length = w
  · subst hl
    exact clzGo_spec xs xs.length x (xs.length - 1) st
  · exact (clzGo_spec xs xs.length (0#xs.length) (xs.length - 1) st).weaken fun env r g _ Hx => by
      exfalso; apply hl; rw [← length_bitsOf x, ← Hx, List.length_map]

/-! ## cpop -/

theorem bitsOf_ofNat_bit {w : Nat} (env : Nat → Bool) (h0 : env 0 = false) (l : Nat) (b : Bool)
    (hl : lv env l = b) (hw : 1 ≤ w) :
    (l :: zeros (w - 1)).map (lv env) = bitsOf (BitVec.ofNat w b.toNat) := by
  rw [List.map_cons, map_zeros env h0, hl]
  apply List.ext_getElem
  · simp [length_bitsOf]; omega
  · intro i h1 h2
    rw [getElem_bitsOf, BitVec.getLsbD_ofNat]
    cases i with
    | zero => cases b <;> simp; omega
    | succ i =>
      simp only [List.getElem_cons_succ, List.getElem_replicate]
      cases b <;> simp [Nat.testBit_succ]

theorem cpopGo_spec (xs : List Nat) (w : Nat) (x : BitVec w) : ∀ (n : Nat) (st : St) (acc : List Nat) (a : Nat),
    n ≤ w →
    Spec av st (cpopGo xs w n st acc) (fun env r =>
      xs.map (lv env) = bitsOf x → acc.map (lv env) = bitsOf (BitVec.ofNat w a) →
        r.map (lv env) = bitsOf (BitVec.ofNat w (BitVec.cpopNatRec x n a)))
  | 0, st, acc, a, _ => Spec.ret fun env _ _ Hacc => by
    rw [Hacc]
    rfl
  | n + 1, st, acc, a, hn => by
    simp only [cpopGo]
    rcases h1 : blastAdd st acc (xs.getD n 0 :: zeros (w - 1)) with ⟨st1, acc1⟩
    have s1 := h1 ▸ blastAdd_spec (av := av) st acc (xs.getD n 0 :: zeros (w - 1))
    dsimp only
    have s2 := cpopGo_spec xs w x n st1 acc1 (a + (x.getLsbD n).toNat) (by omega)
    exact Spec.bind s1 (s2.weaken fun env r g H Hadd Hx Hacc => by
      have hb := bitsOf_ofNat_bit (w := w) env g.1 (xs.getD n 0) (x.getLsbD n) (lv_getD g.1 Hx n) (by omega)
      have hacc1 : acc1.map (lv env) = bitsOf (BitVec.ofNat w (a + (x.getLsbD n).toNat)) := by
        rw [Hadd, Hacc, hb, addL_bitsOf_false, BitVec.ofNat_add]
      rw [H Hx hacc1]
      rfl)

theorem bitsOf_ofNat_zero (w : Nat) : bitsOf (BitVec.ofNat w 0) = List.replicate w false := by
  apply List.ext_getElem
  · simp [length_bitsOf]
  · intro i h1 h2
    rw [getElem_bitsOf, BitVec.getLsbD_ofNat]
    simp

theorem blastCpop_spec (st : St) (xs : List Nat) {w : Nat} (x : BitVec w) :
    Spec av st (blastCpop st xs) (fun env r => xs.map (lv env) = bitsOf x → r.map (lv env) = bitsOf x.cpop) := by
  unfold blastCpop
  by_cases hl : xs.length = w
  · subst hl
    exact (cpopGo_spec xs xs.length x xs.length st (zeros xs.length) 0 (Nat.le_refl _)).weaken
      fun env r g H Hx => H Hx (by rw [map_zeros env g.1, bitsOf_ofNat_zero])
  · exact (cpopGo_spec xs xs.length (0#xs.length) xs.length st (zeros xs.length) 0 (Nat.le_refl _)).weaken
      fun env r g _ Hx => by
        exfalso; apply hl; rw [← length_bitsOf x, ← Hx, List.length_map]

/-! ## All unary operations -/

theorem blastUn_spec (op : BVUnOp) (st : St) (xs : List Nat) {w : Nat} (x : BitVec w) :
    Spec av st (blastUn op st xs) (fun env r => xs.map (lv env) = bitsOf x → r.map (lv env) = bitsOf (op.eval x)) := by
  cases op with
  | clz => exact blastClz_spec st xs x
  | cpop => exact blastCpop_spec st xs x
  | not =>
    refine Spec.ret fun env _ H => ?_
    simp only [unOp]
    rw [List.map_map, show lv env ∘ neg = not ∘ lv env from funext fun l => lv_neg env l,
      ← List.map_map, H, bitsOf_not]; rfl
  | rotateLeft r => exact Spec.ret fun env _ H => by simp only [unOp]; rw [map_rotl, H, rotlL_bitsOf]; rfl
  | rotateRight r => exact Spec.ret fun env _ H => by simp only [unOp]; rw [map_rotr, H, rotrL_bitsOf]; rfl
  | arithShiftRightConst k => exact Spec.ret fun env g H => by simp only [unOp]; rw [map_sarC env g.1, H, sarL_bitsOf]; rfl
  | reverse => exact Spec.ret fun env _ H => by simp only [unOp]; rw [List.map_reverse, H, ← bitsOf_reverse]; rfl

end BVS
