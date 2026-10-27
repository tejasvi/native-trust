module

public import BVS.Sound.Basic

@[expose] public section
/-!
# Soundness of the bit-blaster: circuits over literal lists

Each construction is related to a function on `List Bool` (its value under a valuation).
-/
namespace BVS
open Std.Tactic.BVDecide

variable {av : Nat → Nat → Bool}

theorem Spec.bind {α β : Type} {st a : St} {x : α} {P : (Nat → Bool) → α → Prop}
    (hp : Spec av st (a, x) P) {q : St × β} {Q : (Nat → Bool) → β → Prop}
    (hq : Spec av a q (fun env y => P env x → Q env y)) : Spec av st q Q := by
  refine ⟨hp.1.trans hq.1, fun hinv env g => ?_⟩
  have g1 := Good.mono hq.1 g
  exact hq.2 (hp.1.2 hinv) env g (hp.2 hinv env g1)

theorem Spec.ret {α : Type} {st : St} {x : α} {P : (Nat → Bool) → α → Prop}
    (h : ∀ env, Good av env st → P env x) : Spec av st (st, x) P :=
  ⟨Ext.refl st, fun _ env g => h env g⟩

theorem Spec.ret' {α : Type} {st : St} {x : α} {P : (Nat → Bool) → α → Prop}
    (h : Inv st → ∀ env, Good av env st → P env x) : Spec av st (st, x) P :=
  ⟨Ext.refl st, h⟩

theorem getD_eq_get (xs : List Nat) (j : Nat) (h : j < xs.length) : xs.getD j 0 = xs[j] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]

theorem getD_append_left' (xs ys : List Nat) (j : Nat) (h : j < xs.length) :
    (xs ++ ys).getD j 0 = xs.getD j 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_right' (xs ys : List Nat) (j : Nat) (h : xs.length ≤ j) :
    (xs ++ ys).getD j 0 = ys.getD (j - xs.length) 0 := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_right h]

theorem Spec.weaken {α : Type} {st : St} {p : St × α} {P Q : (Nat → Bool) → α → Prop}
    (h : Spec av st p P) (hPQ : ∀ env y, Good av env p.1 → P env y → Q env y) : Spec av st p Q :=
  ⟨h.1, fun hinv env g => hPQ env _ g (h.2 hinv env g)⟩

theorem Spec.map {α β : Type} {st a : St} {x : α} {y : β} {P : (Nat → Bool) → α → Prop}
    {Q : (Nat → Bool) → β → Prop} (h : Spec av st (a, x) P)
    (hPQ : ∀ env, Good av env a → P env x → Q env y) : Spec av st (a, y) Q :=
  ⟨h.1, fun hinv env g => hPQ env g (h.2 hinv env g)⟩

/-! ## Gates -/

theorem mkOr_spec (st : St) (a b : Nat) :
    Spec av st (mkOr st a b) (fun env o => lv env o = (lv env a || lv env b)) := by
  unfold mkOr
  rcases h : mkAnd st (neg a) (neg b) with ⟨st1, o⟩
  have h1 := h ▸ mkAnd_spec av st (neg a) (neg b)
  dsimp only
  refine Spec.bind h1 (Spec.ret fun env _ H => ?_)
  rw [lv_neg, H, lv_neg, lv_neg]; simp

theorem mkXor_spec (st : St) (a b : Nat) :
    Spec av st (mkXor st a b) (fun env o => lv env o = (lv env a ^^ lv env b)) := by
  unfold mkXor
  rcases h1 : mkAnd st a (neg b) with ⟨st1, x⟩
  have s1 := h1 ▸ mkAnd_spec av st a (neg b)
  dsimp only
  rcases h2 : mkAnd st1 (neg a) b with ⟨st2, y⟩
  have s2 := h2 ▸ mkAnd_spec av st1 (neg a) b
  dsimp only
  refine Spec.bind s1 (Spec.bind s2 ((mkOr_spec st2 x y).weaken fun env o _ H H2 H1 => ?_))
  rw [H, H1, H2, lv_neg, lv_neg]
  cases lv env a <;> cases lv env b <;> rfl

theorem mkXnor_spec (st : St) (a b : Nat) :
    Spec av st (mkXnor st a b) (fun env o => lv env o = (lv env a == lv env b)) := by
  unfold mkXnor
  rcases h : mkXor st a b with ⟨st1, o⟩
  have h1 := h ▸ mkXor_spec (av := av) st a b
  dsimp only
  refine Spec.bind h1 (Spec.ret fun env _ H => ?_)
  rw [lv_neg, H]; cases lv env a <;> cases lv env b <;> rfl

theorem mkMux_spec (st : St) (c a b : Nat) :
    Spec av st (mkMux st c a b) (fun env o => lv env o = (bif lv env c then lv env a else lv env b)) := by
  unfold mkMux
  rcases h1 : mkAnd st c a with ⟨st1, x⟩
  have s1 := h1 ▸ mkAnd_spec av st c a
  dsimp only
  rcases h2 : mkAnd st1 (neg c) b with ⟨st2, y⟩
  have s2 := h2 ▸ mkAnd_spec av st1 (neg c) b
  dsimp only
  refine Spec.bind s1 (Spec.bind s2 ((mkOr_spec st2 x y).weaken fun env o _ H H2 H1 => ?_))
  rw [H, H1, H2, lv_neg]
  cases lv env c <;> cases lv env a <;> cases lv env b <;> rfl

theorem mkMaj_spec (st : St) (a b c : Nat) :
    Spec av st (mkMaj st a b c) (fun env o => lv env o = majB (lv env a) (lv env b) (lv env c)) := by
  unfold mkMaj
  rcases h1 : mkXor st a b with ⟨st1, x⟩
  have s1 := h1 ▸ mkXor_spec (av := av) st a b
  dsimp only
  rcases h2 : mkAnd st1 x c with ⟨st2, t1⟩
  have s2 := h2 ▸ mkAnd_spec av st1 x c
  dsimp only
  rcases h3 : mkAnd st2 a b with ⟨st3, t2⟩
  have s3 := h3 ▸ mkAnd_spec av st2 a b
  dsimp only
  refine Spec.bind s1 (Spec.bind s2 (Spec.bind s3 ((mkOr_spec st3 t1 t2).weaken
    fun env o _ H H3 H2 H1 => ?_)))
  rw [H, H2, H3, H1, majB]

/-! ## Lists of literals -/

theorem zipSt_spec (f : St → Nat → Nat → St × Nat) (g : (Nat → Bool) → Bool → Bool → Bool)
    (hf : ∀ st a b, Spec av st (f st a b) (fun env o => lv env o = g env (lv env a) (lv env b))) :
    ∀ (xs ys : List Nat) (st : St), Spec av st (zipSt f st xs ys)
      (fun env zs => zs.map (lv env) = List.zipWith (g env) (xs.map (lv env)) (ys.map (lv env))) := by
  intro xs
  induction xs with
  | nil => intro ys st; exact Spec.ret fun _ _ => by simp
  | cons x xs ih =>
    intro ys st
    cases ys with
    | nil => exact Spec.ret fun _ _ => by simp
    | cons y ys =>
      unfold zipSt
      rcases h1 : f st x y with ⟨st1, z⟩
      have s1 := h1 ▸ hf st x y
      dsimp only
      rcases h2 : zipSt f st1 xs ys with ⟨st2, zs⟩
      have s2 := h2 ▸ ih ys st1
      dsimp only
      exact Spec.bind s1 (Spec.bind s2 (Spec.ret fun env _ H2 H1 => by simp [H1, H2]))

theorem muxV_spec (st : St) (c : Nat) (xs ys : List Nat) :
    Spec av st (muxV st c xs ys) (fun env zs => zs.map (lv env) =
      List.zipWith (fun a b => bif lv env c then a else b) (xs.map (lv env)) (ys.map (lv env))) :=
  zipSt_spec (fun st a b => mkMux st c a b) (fun env a b => bif lv env c then a else b)
    (fun st a b => mkMux_spec st c a b) xs ys st

/-! ### Lengths -/

theorem length_takeDL (n : Nat) (l : List Bool) : (takeDL n l).length = n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [takeDL, ih]

theorem length_addL : ∀ (as bs : List Bool) (c : Bool), (addL as bs c).1.length = min as.length bs.length
  | [], _, _ => by simp [addL]
  | _ :: _, [], _ => by simp [addL]
  | a :: as, b :: bs, c => by simp [addL, length_addL as bs, Nat.min_def]; split <;> omega

theorem length_zipSt {f : St → Nat → Nat → St × Nat} :
    ∀ (xs ys : List Nat) (st : St), (zipSt f st xs ys).2.length = min xs.length ys.length
  | [], _, _ => by simp [zipSt]
  | _ :: _, [], _ => by simp [zipSt]
  | x :: xs, y :: ys, st => by
    simp only [zipSt]
    rcases f st x y with ⟨st1, z⟩
    dsimp only
    have := length_zipSt (f := f) xs ys st1
    rcases h : zipSt f st1 xs ys with ⟨st2, zs⟩
    rw [h] at this
    simp only at this ⊢
    rw [List.length_cons, this, List.length_cons, List.length_cons, Nat.succ_min_succ]

theorem zipWith_mux {c : Bool} {xs ys : List Bool} (h : xs.length = ys.length) :
    List.zipWith (fun a b => bif c then a else b) xs ys = if c then xs else ys := by
  induction xs generalizing ys with
  | nil => cases ys <;> simp_all
  | cons x xs ih =>
    cases ys with
    | nil => simp at h
    | cons y ys =>
      simp only [List.length_cons, Nat.add_right_cancel_iff] at h
      simp only [List.zipWith_cons_cons, ih h]
      cases c <;> rfl

/-! ### Lists of constant literals -/

theorem map_zeros (env : Nat → Bool) (h : env 0 = false) (n : Nat) :
    (zeros n).map (lv env) = List.replicate n false := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeros, List.replicate_succ, ih, lv_zero h]

theorem length_zeros (n : Nat) : (zeros n).length = n := by
  induction n with
  | zero => rfl
  | succ n ih => simp [zeros, ih]

theorem map_takeD (env : Nat → Bool) (h : env 0 = false) :
    ∀ (n : Nat) (l : List Nat), (takeD n l).map (lv env) = takeDL n (l.map (lv env))
  | 0, _ => rfl
  | n + 1, [] => by simp [takeD, takeDL, map_takeD env h n [], lv_zero h]
  | n + 1, x :: xs => by simp [takeD, takeDL, map_takeD env h n xs]

theorem map_shl (env : Nat → Bool) (h : env 0 = false) (xs : List Nat) (i : Nat) :
    (shl xs i).map (lv env) = shlL (xs.map (lv env)) i := by
  simp [shl, shlL, map_takeD env h, map_zeros env h]

theorem map_shiftConcat (env : Nat → Bool) (h : env 0 = false) (xs : List Nat) (b : Nat) :
    (shiftConcat xs b).map (lv env) = shiftConcatL (xs.map (lv env)) (lv env b) := by
  simp [shiftConcat, shiftConcatL, map_takeD env h]

theorem getD_map_lv (env : Nat → Bool) (h : env 0 = false) (xs : List Nat) (i : Nat) :
    lv env (xs.getD i 0) = (xs.map (lv env)).getD i false := by
  induction xs generalizing i with
  | nil => simp only [List.getD_nil, List.map_nil, lv_zero h]
  | cons x xs ih =>
    cases i with
    | zero => simp only [List.getD_cons_zero, List.map_cons]
    | succ i => simp only [List.getD_cons_succ, List.map_cons]; exact ih i

/-! ### Adders -/

theorem addGo_spec : ∀ (xs ys : List Nat) (st : St) (c : Nat),
    Spec av st (addGo st xs ys c) (fun env r =>
      r.1.map (lv env) = (addL (xs.map (lv env)) (ys.map (lv env)) (lv env c)).1 ∧
      lv env r.2 = (addL (xs.map (lv env)) (ys.map (lv env)) (lv env c)).2)
  | [], _, st, c => Spec.ret fun _ _ => by simp [addL]
  | _ :: _, [], st, c => Spec.ret fun _ _ => by simp [addL]
  | a :: as, b :: bs, st, c => by
    unfold addGo
    rcases h1 : mkXor st a b with ⟨st1, x⟩
    have s1 := h1 ▸ mkXor_spec (av := av) st a b
    dsimp only
    rcases h2 : mkXor st1 x c with ⟨st2, s⟩
    have s2 := h2 ▸ mkXor_spec (av := av) st1 x c
    dsimp only
    rcases h3 : mkAnd st2 x c with ⟨st3, t1⟩
    have s3 := h3 ▸ mkAnd_spec av st2 x c
    dsimp only
    rcases h4 : mkAnd st3 a b with ⟨st4, t2⟩
    have s4 := h4 ▸ mkAnd_spec av st3 a b
    dsimp only
    rcases h5 : mkOr st4 t1 t2 with ⟨st5, c'⟩
    have s5 := h5 ▸ mkOr_spec (av := av) st4 t1 t2
    dsimp only
    rcases h6 : addGo st5 as bs c' with ⟨st6, ss, co⟩
    have s6 := h6 ▸ addGo_spec as bs st5 c'
    dsimp only
    refine Spec.bind s1 (Spec.bind s2 (Spec.bind s3 (Spec.bind s4 (Spec.bind s5 (Spec.bind s6
      (Spec.ret fun env _ H6 H5 H4 H3 H2 H1 => ?_))))))
    have hc' : lv env c' = majB (lv env a) (lv env b) (lv env c) := by
      rw [H5, H3, H4, H1, majB]
    simp only [List.map_cons, addL]
    rw [← hc']
    exact ⟨by rw [H6.1, H2, H1], H6.2⟩

theorem length_addGo : ∀ (xs ys : List Nat) (st : St) (c : Nat),
    (addGo st xs ys c).2.1.length = min xs.length ys.length
  | [], _, _, _ => by simp [addGo]
  | _ :: _, [], _, _ => by simp [addGo]
  | a :: as, b :: bs, st, c => by
    simp only [addGo]
    rcases mkXor st a b with ⟨st1, x⟩
    rcases mkXor st1 x c with ⟨st2, s⟩
    rcases mkAnd st2 x c with ⟨st3, t1⟩
    rcases mkAnd st3 a b with ⟨st4, t2⟩
    rcases mkOr st4 t1 t2 with ⟨st5, c'⟩
    dsimp only
    have := length_addGo as bs st5 c'
    rcases h : addGo st5 as bs c' with ⟨st6, ss, co⟩
    rw [h] at this
    simp only at this ⊢
    rw [List.length_cons, this, List.length_cons, List.length_cons, Nat.succ_min_succ]

theorem length_blastAdd (st : St) (xs ys : List Nat) :
    (blastAdd st xs ys).2.length = min xs.length ys.length := by
  unfold blastAdd
  have := length_addGo xs ys st 0
  rcases h : addGo st xs ys 0 with ⟨st1, ss, co⟩
  rw [h] at this
  exact this

theorem length_takeD (n : Nat) (l : List Nat) : (takeD n l).length = n := by
  induction n generalizing l with
  | zero => rfl
  | succ n ih => cases l <;> simp [takeD, ih]

theorem length_shl (xs : List Nat) (i : Nat) : (shl xs i).length = xs.length := by
  simp [shl, length_takeD]

theorem blastAdd_spec (st : St) (xs ys : List Nat) :
    Spec av st (blastAdd st xs ys) (fun env r =>
      r.map (lv env) = (addL (xs.map (lv env)) (ys.map (lv env)) false).1) := by
  unfold blastAdd
  rcases h : addGo st xs ys 0 with ⟨st1, ss, co⟩
  have s := h ▸ addGo_spec (av := av) xs ys st 0
  dsimp only
  exact s.map fun env g H => by rw [H.1, g.lv0]

theorem carryGo_spec : ∀ (xs ys : List Nat) (st : St) (c : Nat),
    Spec av st (carryGo st xs ys c) (fun env r =>
      lv env r = (addL (xs.map (lv env)) (ys.map (lv env)) (lv env c)).2)
  | [], _, st, c => Spec.ret fun _ _ => by simp [addL]
  | _ :: _, [], st, c => Spec.ret fun _ _ => by simp [addL]
  | a :: as, b :: bs, st, c => by
    unfold carryGo
    rcases h1 : mkMaj st a b c with ⟨st1, c'⟩
    have s1 := h1 ▸ mkMaj_spec (av := av) st a b c
    dsimp only
    exact Spec.bind s1 ((carryGo_spec as bs st1 c').weaken fun env _ _ H H1 => by
      simp only [List.map_cons, addL]; rw [H, H1])

theorem blastUlt_spec (st : St) (xs ys : List Nat) :
    Spec av st (blastUlt st xs ys) (fun env r =>
      lv env r = !(addL (xs.map (lv env)) ((ys.map (lv env)).map not) true).2) := by
  unfold blastUlt
  rcases h : carryGo st xs (ys.map neg) 1 with ⟨st1, c⟩
  have s := h ▸ carryGo_spec (av := av) xs (ys.map neg) st 1
  dsimp only
  refine s.map fun env g H => ?_
  rw [lv_neg, H, g.lv1]
  congr 3
  simp [List.map_map, Function.comp_def, lv_neg]

theorem andAll_spec : ∀ (zs : List Nat) (st : St),
    Spec av st (andAll st zs) (fun env r => lv env r = allL (zs.map (lv env)))
  | [], st => Spec.ret fun _ g => by simp [allL, g.lv1]
  | z :: zs, st => by
    unfold andAll
    rcases h1 : andAll st zs with ⟨st1, r⟩
    have s1 := h1 ▸ andAll_spec zs st
    dsimp only
    exact Spec.bind s1 ((mkAnd_spec av st1 z r).weaken fun env _ _ H H1 => by
      simp only [List.map_cons, allL]; rw [H, H1])

theorem blastEq_spec (st : St) (xs ys : List Nat) :
    Spec av st (blastEq st xs ys) (fun env r =>
      lv env r = allL (List.zipWith (· == ·) (xs.map (lv env)) (ys.map (lv env)))) := by
  unfold blastEq
  rcases h : zipSt mkXnor st xs ys with ⟨st1, zs⟩
  have s := h ▸ zipSt_spec (av := av) mkXnor (fun _ a b => a == b) (fun st a b => mkXnor_spec st a b) xs ys st
  dsimp only
  exact Spec.bind s ((andAll_spec zs st1).weaken fun env _ _ H H1 => by rw [H, H1])

/-! ### Multiplication -/

theorem mulGo_spec (xs : List Nat) : ∀ (ys : List Nat) (st : St) (i : Nat) (acc : List Nat),
    acc.length = xs.length →
    Spec av st (mulGo xs st ys i acc) (fun env r =>
      r.map (lv env) = mulL (xs.map (lv env)) (ys.map (lv env)) i (acc.map (lv env)))
  | [], st, i, acc, _ => Spec.ret fun _ _ => by simp [mulL]
  | y :: ys, st, i, acc, hacc => by
    unfold mulGo
    simp only [nat_beq_eq, cond_decide]
    by_cases hy : y = 0
    · simp only [hy, if_true]
      refine (mulGo_spec xs ys st (i + 1) acc hacc).weaken fun env _ g H => ?_
      rw [H]; simp [mulL, lv_zero g.1]
    · simp only [hy, if_false]
      rcases h1 : blastAdd st acc (shl xs i) with ⟨st1, sum⟩
      have s1 := h1 ▸ blastAdd_spec (av := av) st acc (shl xs i)
      dsimp only
      rcases h2 : muxV st1 y sum acc with ⟨st2, acc'⟩
      have s2 := h2 ▸ muxV_spec (av := av) st1 y sum acc
      dsimp only
      -- lengths
      have hsum : sum.length = acc.length := by
        have := length_blastAdd st acc (shl xs i)
        rw [h1] at this; simp only at this; rw [this, length_shl, hacc, Nat.min_self]
      have hacc' : acc'.length = xs.length := by
        have := length_zipSt (f := fun st a b => mkMux st y a b) sum acc st1
        have e : zipSt (fun st a b => mkMux st y a b) st1 sum acc = muxV st1 y sum acc := rfl
        rw [e, h2] at this
        simp only at this; rw [this, hsum, hacc, Nat.min_self]
      refine Spec.bind s1 (Spec.bind s2 ((mulGo_spec xs ys st2 (i + 1) acc' hacc').weaken
        fun env _ g H H2 H1 => ?_))
      rw [H, H2, H1]
      simp only [List.map_cons, mulL]
      congr 1
      rw [zipWith_mux, map_shl env g.1]
      rw [← H1, List.length_map, List.length_map, hsum]

/-! ### Division -/

theorem length_shiftConcat (xs : List Nat) (b : Nat) : (shiftConcat xs b).length = xs.length := by
  simp [shiftConcat, length_takeD]

theorem length_muxV (st : St) (c : Nat) (xs ys : List Nat) :
    (muxV st c xs ys).2.length = min xs.length ys.length :=
  length_zipSt xs ys st

theorem length_divStep (n d : List Nat) (wn : Nat) (q r : List Nat) (st : St)
    (hq : q.length = d.length) (hr : r.length = d.length) :
    (divStep st n d wn q r).2.1.length = d.length ∧ (divStep st n d wn q r).2.2.length = d.length := by
  unfold divStep
  dsimp only
  rcases h1 : addGo st (shiftConcat r (n.getD (wn - 1) 0)) (d.map neg) 1 with ⟨st1, diff, c⟩
  have l1 : diff.length = d.length := by
    have := length_addGo (shiftConcat r (n.getD (wn - 1) 0)) (d.map neg) st 1
    rw [h1] at this; simp only at this
    rw [this, length_shiftConcat, hr, List.length_map, Nat.min_self]
  dsimp only
  rcases h2 : muxV st1 c (shiftConcat q 1) (shiftConcat q 0) with ⟨st2, q'⟩
  have l2 : q'.length = d.length := by
    have := length_muxV st1 c (shiftConcat q 1) (shiftConcat q 0)
    rw [h2] at this; simp only at this
    rw [this, length_shiftConcat, length_shiftConcat, hq, Nat.min_self]
  dsimp only
  rcases h3 : muxV st2 c diff (shiftConcat r (n.getD (wn - 1) 0)) with ⟨st3, r''⟩
  have l3 : r''.length = d.length := by
    have := length_muxV st2 c diff (shiftConcat r (n.getD (wn - 1) 0))
    rw [h3] at this; simp only at this
    rw [this, l1, length_shiftConcat, hr, Nat.min_self]
  exact ⟨l2, l3⟩

theorem divStep_spec (n d : List Nat) (wn : Nat) (q r : List Nat) (st : St)
    (hr : r.length = d.length) :
    Spec av st (divStep st n d wn q r) (fun env res =>
      res.1.map (lv env) = (divStepL (n.map (lv env)) (d.map (lv env)) wn (q.map (lv env)) (r.map (lv env))).1 ∧
      res.2.map (lv env) = (divStepL (n.map (lv env)) (d.map (lv env)) wn (q.map (lv env)) (r.map (lv env))).2) := by
  unfold divStep
  dsimp only
  rcases h1 : addGo st (shiftConcat r (n.getD (wn - 1) 0)) (d.map neg) 1 with ⟨st1, diff, c⟩
  have s1 := h1 ▸ addGo_spec (av := av) (shiftConcat r (n.getD (wn - 1) 0)) (d.map neg) st 1
  have l1 : diff.length = d.length := by
    have := length_addGo (shiftConcat r (n.getD (wn - 1) 0)) (d.map neg) st 1
    rw [h1] at this; simp only at this
    rw [this, length_shiftConcat, hr, List.length_map, Nat.min_self]
  dsimp only
  rcases h2 : muxV st1 c (shiftConcat q 1) (shiftConcat q 0) with ⟨st2, q'⟩
  have s2 := h2 ▸ muxV_spec (av := av) st1 c (shiftConcat q 1) (shiftConcat q 0)
  dsimp only
  rcases h3 : muxV st2 c diff (shiftConcat r (n.getD (wn - 1) 0)) with ⟨st3, r''⟩
  have s3 := h3 ▸ muxV_spec (av := av) st2 c diff (shiftConcat r (n.getD (wn - 1) 0))
  dsimp only
  refine Spec.bind s1 (Spec.bind s2 (Spec.bind s3 (Spec.ret fun env g H3 H2 H1 => ?_)))
  have e0 := g.1
  have hd : (d.map neg).map (lv env) = (d.map (lv env)).map not := by
    simp [List.map_map, Function.comp_def, lv_neg]
  have hn : lv env (n.getD (wn - 1) 0) = (n.map (lv env)).getD (wn - 1) false := getD_map_lv env e0 n _
  rw [map_shiftConcat env e0, hn, hd, lv_one e0] at H1
  refine ⟨?_, ?_⟩
  · rw [H2, zipWith_mux, map_shiftConcat env e0, map_shiftConcat env e0, lv_one e0, lv_zero e0, H1.2]
    · simp only [divStepL]
    · simp [length_shiftConcat]
  · rw [H3, zipWith_mux, H1.1, map_shiftConcat env e0, hn, H1.2]
    · simp only [divStepL]
    · rw [List.length_map, List.length_map, l1, length_shiftConcat, hr]

theorem divGo_spec (n d : List Nat) : ∀ (k wn : Nat) (q r : List Nat) (st : St),
    q.length = d.length → r.length = d.length →
    Spec av st (divGo n d st k wn q r) (fun env res =>
      res.1.map (lv env) = (divGoL (n.map (lv env)) (d.map (lv env)) k wn (q.map (lv env)) (r.map (lv env))).1 ∧
      res.2.map (lv env) = (divGoL (n.map (lv env)) (d.map (lv env)) k wn (q.map (lv env)) (r.map (lv env))).2)
  | 0, wn, q, r, st, _, _ => Spec.ret fun _ _ => by simp [divGoL]
  | k + 1, wn, q, r, st, hq, hr => by
    unfold divGo
    have hl := length_divStep n d wn q r st hq hr
    rcases h1 : divStep st n d wn q r with ⟨st1, q', r'⟩
    have s1 := h1 ▸ divStep_spec (av := av) n d wn q r st hr
    rw [h1] at hl
    dsimp only
    exact Spec.bind s1 ((divGo_spec n d k (wn - 1) q' r' st1 hl.1 hl.2).weaken fun env _ _ H H1 => by
      simp only [divGoL]; rw [← H1.1, ← H1.2]; exact H)

theorem length_divGo (n d : List Nat) : ∀ (k wn : Nat) (q r : List Nat) (st : St),
    q.length = d.length → r.length = d.length →
    (divGo n d st k wn q r).2.1.length = d.length ∧ (divGo n d st k wn q r).2.2.length = d.length
  | 0, _, _, _, _, hq, hr => ⟨hq, hr⟩
  | k + 1, wn, q, r, st, hq, hr => by
    unfold divGo
    have hl := length_divStep n d wn q r st hq hr
    rcases h1 : divStep st n d wn q r with ⟨st1, q', r'⟩
    rw [h1] at hl
    exact length_divGo n d k (wn - 1) q' r' st1 hl.1 hl.2

/-! ### Input bits -/

theorem allocAtoms_spec (v : Nat) : ∀ (c i : Nat) (st : St),
    Ext st (allocAtoms v st i c).1 ∧ (allocAtoms v st i c).2.length = c ∧
    (∀ j, j < c → Ent.atom ((allocAtoms v st i c).2.getD j 0) v (i + j) ∈ (allocAtoms v st i c).1.es) ∧
    (allocAtoms v st i c).1.ha = st.ha ∧ (allocAtoms v st i c).1.mb = st.mb ∧
    (allocAtoms v st i c).1.md = st.md
  | 0, i, st => ⟨Ext.refl st, rfl, fun j h => absurd h (by omega), rfl, rfl, rfl⟩
  | c + 1, i, st => by
    have ih := allocAtoms_spec v c (i + 1) { st with n := st.n + 1, es := .atom st.n v i :: st.es }
    simp only [allocAtoms]
    generalize allocAtoms v { st with n := st.n + 1, es := .atom st.n v i :: st.es } (i + 1) c = p at ih ⊢
    rcases p with ⟨st', ks⟩
    dsimp only at ih ⊢
    obtain ⟨e1, l1, m1, a1, b1, d1⟩ := ih
    have ext0 : Ext st { st with n := st.n + 1, es := .atom st.n v i :: st.es } := by
      refine ⟨fun e he => List.mem_cons_of_mem _ he, fun hinv => ⟨?_, ?_⟩⟩
      · intro v' ks' hks i' hi'; exact List.mem_cons_of_mem _ (hinv.1 v' ks' hks i' hi')
      · exact hinv.2.mono rfl rfl (fun e he => List.mem_cons_of_mem _ he)
    refine ⟨ext0.trans e1, by simp [l1], fun j hj => ?_, a1, b1, d1⟩
    cases j with
    | zero => simp only [List.getD_cons_zero, Nat.add_zero]; exact e1.1 _ (List.mem_cons_self ..)
    | succ j =>
      simp only [List.getD_cons_succ]
      have := m1 j (by omega)
      rw [show i + (j + 1) = i + 1 + j by omega]; exact this

theorem map_dbl_eq (env : Nat → Bool) (av' : Nat → Bool) (xs : List Nat) (w : Nat) (hl : xs.length = w)
    (h : ∀ j, j < w → env (xs.getD j 0) = av' j) : (dbl xs).map (lv env) = (List.range w).map av' := by
  apply List.ext_getElem
  · simp [dbl, hl]
  · intro j h1 h2
    simp only [dbl, List.map_map, List.getElem_map, List.getElem_range, Function.comp_apply, lv_two_mul]
    have hj : j < w := by simpa [dbl, hl] using h1
    rw [← h j hj, getD_eq_get]

theorem blastVar_spec (st : St) (v w : Nat) :
    Spec av st (blastVar st v w) (fun env r => r.map (lv env) = (List.range w).map (av v)) := by
  unfold blastVar
  simp only [nat_ble_eq, cond_decide]
  generalize hks : (st.ha.get v).getD [] = ks
  -- the cached bits are atoms of `v`
  have hat : Inv st → ∀ j, j < ks.length → Ent.atom (ks.getD j 0) v j ∈ st.es := by
    intro hinv j hj
    cases hg : st.ha.get v with
    | none => rw [hg] at hks; subst hks; simp at hj
    | some ks0 =>
      rw [hg] at hks; simp only [Option.getD] at hks; subst hks
      rw [getD_eq_get _ _ hj]; exact hinv.1 v ks0 hg j hj
  by_cases hw : w ≤ ks.length
  · simp only [hw, if_true]
    refine Spec.ret' fun hinv env g => ?_
    apply map_dbl_eq env (av v) _ w (by simp [hw])
    intro j hj
    have hj' : j < ks.length := by omega
    have := g.2 _ (hat hinv j hj')
    simp only [Ent.holds] at this
    rw [← this]
    simp [List.getD_eq_getElem?_getD, hj]
  · simp only [hw, if_false]
    have ha := allocAtoms_spec v (w - ks.length) ks.length st
    generalize allocAtoms v st ks.length (w - ks.length) = p at ha ⊢
    rcases p with ⟨st', ks'⟩
    obtain ⟨e1, l1, m1, a1, b1, d1⟩ := ha
    simp only at e1 l1 m1 a1 ⊢
    -- all bits of the new list are atoms of `v` in `st'`
    have hall : Inv st → ∀ j, j < (ks ++ ks').length → Ent.atom ((ks ++ ks').getD j 0) v j ∈ st'.es := by
      intro hinv j hj
      by_cases hjk : j < ks.length
      · rw [getD_append_left' _ _ _ hjk]; exact e1.1 _ (hat hinv j hjk)
      · rw [getD_append_right' _ _ _ (by omega)]
        have := m1 (j - ks.length) (by simp at hj; omega)
        rw [show ks.length + (j - ks.length) = j by omega] at this; exact this
    have ext2 : Ext st { st' with ha := st'.ha.upd 64 v (fun _ => ks ++ ks') } := by
      refine ⟨e1.1, fun hinv => ⟨?_, (e1.2 hinv).2.mono rfl rfl (fun e he => he)⟩⟩
      intro v' ks'' hg j hj
      simp only at hg ⊢
      rcases NT.get_upd 64 st'.ha v _ v' ks'' hg with ⟨e3, e4⟩ | e5
      · subst e3; subst e4; rw [← getD_eq_get _ _ hj]; exact hall hinv j hj
      · exact (e1.2 hinv).1 v' ks'' e5 j hj
    refine ⟨ext2, fun hinv env g => ?_⟩
    simp only
    apply map_dbl_eq env (av v) _ w (by simp [l1]; omega)
    intro j hj
    have := g.2 _ (hall hinv j (by simp [l1]; omega))
    simp only [Ent.holds] at this
    exact this

/-! ### Extension without length hypotheses -/

theorem ext_divStep (n d : List Nat) (wn : Nat) (q r : List Nat) (st : St) :
    Ext st (divStep st n d wn q r).1 := by
  unfold divStep
  dsimp only
  rcases h1 : addGo st (shiftConcat r (n.getD (wn - 1) 0)) (d.map neg) 1 with ⟨st1, diff, c⟩
  have s1 := h1 ▸ (addGo_spec (av := fun _ _ => false) (shiftConcat r (n.getD (wn - 1) 0)) (d.map neg) st 1).1
  dsimp only
  rcases h2 : muxV st1 c (shiftConcat q 1) (shiftConcat q 0) with ⟨st2, q'⟩
  have s2 := h2 ▸ (muxV_spec (av := fun _ _ => false) st1 c (shiftConcat q 1) (shiftConcat q 0)).1
  dsimp only
  rcases h3 : muxV st2 c diff (shiftConcat r (n.getD (wn - 1) 0)) with ⟨st3, r''⟩
  have s3 := h3 ▸ (muxV_spec (av := fun _ _ => false) st2 c diff (shiftConcat r (n.getD (wn - 1) 0))).1
  exact s1.trans (s2.trans s3)

theorem ext_divGo (n d : List Nat) : ∀ (k wn : Nat) (q r : List Nat) (st : St),
    Ext st (divGo n d st k wn q r).1
  | 0, _, _, _, st => Ext.refl st
  | k + 1, wn, q, r, st => by
    unfold divGo
    have e1 := ext_divStep n d wn q r st
    rcases h1 : divStep st n d wn q r with ⟨st1, q', r'⟩
    rw [h1] at e1
    exact e1.trans (ext_divGo n d k (wn - 1) q' r' st1)

theorem length_shiftConcatL (l : List Bool) (b : Bool) : (shiftConcatL l b).length = l.length := by
  simp [shiftConcatL, length_takeDL]

theorem length_divGoL (n d : List Bool) : ∀ (k wn : Nat) (q r : List Bool),
    q.length = d.length → r.length = d.length →
    (divGoL n d k wn q r).1.length = d.length ∧ (divGoL n d k wn q r).2.length = d.length
  | 0, _, _, _, hq, hr => ⟨hq, hr⟩
  | k + 1, wn, q, r, hq, hr => by
    simp only [divGoL]
    apply length_divGoL
    · simp only [divStepL]; split <;> simp [length_shiftConcatL, hq]
    · simp only [divStepL]
      split
      · rw [length_addL]; simp [length_shiftConcatL, hr]
      · simp [length_shiftConcatL, hr]

/-! ### The divider memo -/

theorem listEq_eq : ∀ (a b : List Nat), listEq a b = true → a = b
  | [], [], _ => rfl
  | x :: xs, y :: ys, h => by
    simp only [listEq, Bool.and_eq_true] at h
    rw [Nat.eq_of_beq_eq_true h.1, listEq_eq xs ys h.2]
  | [], _ :: _, h => by simp [listEq] at h
  | _ :: _, [], h => by simp [listEq] at h

theorem findMD_mem (xs ys : List Nat) : ∀ (md : List (List Nat × List Nat × Nat × List Nat × List Nat))
    (z : Nat) (q r : List Nat), findMD xs ys md = some (z, q, r) → (xs, ys, z, q, r) ∈ md
  | [], _, _, _, h => by simp [findMD] at h
  | (a, b, z', q', r') :: rest, z, q, r, h => by
    simp only [findMD, Bool.and_eq_true] at h
    cases hc : (listEq a xs && listEq b ys)
    · rw [hc] at h; simp only [cond] at h
      exact List.mem_cons_of_mem _ (findMD_mem xs ys rest z q r h)
    · rw [hc] at h; simp only [cond, Option.some.injEq, Prod.mk.injEq] at h
      simp only [Bool.and_eq_true] at hc
      rw [listEq_eq _ _ hc.1, listEq_eq _ _ hc.2] at *
      obtain ⟨rfl, rfl, rfl⟩ := h
      exact List.mem_cons_self ..

/-- The semantics of a divider result. -/
def DivSem (env : Nat → Bool) (xs ys : List Nat) (z : Nat) (q r : List Nat) : Prop :=
  ys.length = xs.length →
    lv env z = allL (List.zipWith (· == ·) (ys.map (lv env)) (List.replicate xs.length false)) ∧
    q.map (lv env) = (divGoL (xs.map (lv env)) (ys.map (lv env)) xs.length xs.length
      (List.replicate xs.length false) (List.replicate xs.length false)).1 ∧
    r.map (lv env) = (divGoL (xs.map (lv env)) (ys.map (lv env)) xs.length xs.length
      (List.replicate xs.length false) (List.replicate xs.length false)).2

theorem divMemo_spec (st : St) (xs ys : List Nat) :
    Spec av st (divMemo st xs ys) (fun env res => DivSem env xs ys res.1 res.2.1 res.2.2) := by
  unfold divMemo
  cases hf : findMD xs ys st.md with
  | some zqr =>
    obtain ⟨z, q, r⟩ := zqr
    exact Spec.ret' fun hinv env g => (hinv.2 av env g).2 xs ys z q r (findMD_mem xs ys st.md z q r hf)
  | none =>
    dsimp only
    rcases h1 : blastEq st ys (zeros xs.length) with ⟨st1, z⟩
    dsimp only
    have e2 := ext_divGo xs ys xs.length xs.length (zeros xs.length) (zeros xs.length) st1
    rcases h2 : divGo xs ys st1 xs.length xs.length (zeros xs.length) (zeros xs.length) with ⟨st2, q, r⟩
    rw [h2] at e2
    dsimp only
    have e1 := (h1 ▸ blastEq_spec (av := av) st ys (zeros xs.length)).1
    -- the semantics of the new entry, for any bit valuation
    have hsem : ∀ av' env, Inv st → Good av' env st2 → DivSem env xs ys z q r := by
      intro av' env hinv g hl
      have s1 := h1 ▸ blastEq_spec (av := av') st ys (zeros xs.length)
      have s2 := h2 ▸ divGo_spec (av := av') xs ys xs.length xs.length (zeros xs.length) (zeros xs.length) st1
        (by rw [length_zeros, hl]) (by rw [length_zeros, hl])
      have H1 := s1.2 hinv env (Good.mono e2 g)
      have H2 := s2.2 (s1.1.2 hinv) env g
      simp only at H1 H2
      rw [map_zeros env g.1] at H1 H2
      exact ⟨H1, H2.1, H2.2⟩
    have ext3 : Ext st { st2 with md := (xs, ys, z, q, r) :: st2.md } := by
      refine ⟨fun e he => e2.1 _ (e1.1 _ he), fun hinv => ?_⟩
      have hinv2 := e2.2 (e1.2 hinv)
      refine ⟨hinv2.1, ?_⟩
      intro av' env g
      obtain ⟨m1, m2⟩ := hinv2.2 av' env g
      exact ⟨m1, fun xs' ys' z' q' r' hm => by
        rcases List.mem_cons.mp hm with he | he
        · simp only [Prod.mk.injEq] at he
          obtain ⟨rfl, rfl, rfl, rfl, rfl⟩ := he
          exact hsem av' env hinv g
        · exact m2 xs' ys' z' q' r' he⟩
    exact ⟨ext3, fun hinv env g => hsem av env hinv g⟩

theorem blastUdiv_spec (st : St) (xs ys : List Nat) :
    Spec av st (blastUdiv st xs ys) (fun env r => ys.length = xs.length → r.map (lv env) =
      if allL (List.zipWith (· == ·) (ys.map (lv env)) (List.replicate xs.length false)) then
        List.replicate xs.length false
      else (divGoL (xs.map (lv env)) (ys.map (lv env)) xs.length xs.length
        (List.replicate xs.length false) (List.replicate xs.length false)).1) := by
  unfold blastUdiv
  rcases h1 : divMemo st xs ys with ⟨st1, z, q, r⟩
  have s1 := h1 ▸ divMemo_spec (av := av) st xs ys
  dsimp only
  refine Spec.bind s1 ((muxV_spec st1 z (zeros xs.length) q).weaken fun env _ g H H1 hl => ?_)
  obtain ⟨Hz, Hq, _⟩ := H1 hl
  rw [H, zipWith_mux, Hz, map_zeros env g.1, Hq]
  rw [List.length_map, List.length_map, length_zeros]
  have := congrArg List.length Hq
  simp only [List.length_map] at this
  rw [this, (length_divGoL _ _ _ _ _ _ (by simp [hl]) (by simp [hl])).1, List.length_map, hl]

theorem blastUmod_spec (st : St) (xs ys : List Nat) :
    Spec av st (blastUmod st xs ys) (fun env r => ys.length = xs.length → r.map (lv env) =
      if allL (List.zipWith (· == ·) (ys.map (lv env)) (List.replicate xs.length false)) then
        xs.map (lv env)
      else (divGoL (xs.map (lv env)) (ys.map (lv env)) xs.length xs.length
        (List.replicate xs.length false) (List.replicate xs.length false)).2) := by
  unfold blastUmod
  rcases h1 : divMemo st xs ys with ⟨st1, z, q, r⟩
  have s1 := h1 ▸ divMemo_spec (av := av) st xs ys
  dsimp only
  refine Spec.bind s1 ((muxV_spec st1 z xs r).weaken fun env _ g H H1 hl => ?_)
  obtain ⟨Hz, _, Hr⟩ := H1 hl
  rw [H, zipWith_mux, Hz, Hr]
  rw [List.length_map, List.length_map]
  have := congrArg List.length Hr
  simp only [List.length_map] at this
  rw [this, (length_divGoL _ _ _ _ _ _ (by simp [hl]) (by simp [hl])).2, List.length_map, hl]

/-! ### Word operations and their memo -/

theorem blastBinRaw_spec (op : BVBinOp) (st : St) (xs ys : List Nat) :
    Spec av st (blastBinRaw op st xs ys) (fun env r => ys.length = xs.length →
      r.map (lv env) = binSemC (opCode op) (xs.map (lv env)) (ys.map (lv env))) := by
  cases op with
  | and =>
    exact Spec.weaken (zipSt_spec mkAnd (fun _ a b => a && b) (fun st a b => mkAnd_spec _ st a b) xs ys st)
      (fun env r _ H _ => H)
  | or =>
    exact Spec.weaken (zipSt_spec mkOr (fun _ a b => a || b) (fun st a b => mkOr_spec st a b) xs ys st)
      (fun env r _ H _ => H)
  | xor =>
    exact Spec.weaken (zipSt_spec mkXor (fun _ a b => a ^^ b) (fun st a b => mkXor_spec st a b) xs ys st)
      (fun env r _ H _ => H)
  | add => exact Spec.weaken (blastAdd_spec st xs ys) (fun env r _ H _ => H)
  | mul =>
    have S := mulGo_spec (av := av) xs ys st 0 (zeros xs.length) (length_zeros _)
    exact Spec.weaken S (fun env r g H _ => by
      rw [H, map_zeros env g.1]; simp [binSemC, opCode])
  | udiv =>
    exact Spec.weaken (blastUdiv_spec st xs ys) (fun env r _ H hl => by rw [H hl]; simp [binSemC, opCode])
  | umod =>
    exact Spec.weaken (blastUmod_spec st xs ys) (fun env r _ H hl => by rw [H hl]; simp [binSemC, opCode])

theorem findMB_mem (c : Nat) (xs ys : List Nat) : ∀ (mb : List (Nat × List Nat × List Nat × List Nat))
    (zs : List Nat), findMB c xs ys mb = some zs → (c, xs, ys, zs) ∈ mb
  | [], _, h => by simp [findMB] at h
  | (o, a, b, z) :: rest, zs, h => by
    simp only [findMB] at h
    cases hc : (Nat.beq o c && listEq a xs && listEq b ys)
    · rw [hc] at h; simp only [cond] at h
      exact List.mem_cons_of_mem _ (findMB_mem c xs ys rest zs h)
    · rw [hc] at h; simp only [cond, Option.some.injEq] at h
      simp only [Bool.and_eq_true] at hc
      have e1 := Nat.eq_of_beq_eq_true hc.1.1
      have e2 := listEq_eq _ _ hc.1.2
      have e3 := listEq_eq _ _ hc.2
      subst e1 e2 e3 h
      exact List.mem_cons_self ..

theorem blastBin_spec (op : BVBinOp) (st : St) (xs ys : List Nat) :
    Spec av st (blastBin op st xs ys) (fun env r => ys.length = xs.length →
      r.map (lv env) = binSemC (opCode op) (xs.map (lv env)) (ys.map (lv env))) := by
  unfold blastBin
  cases hf : findMB (opCode op) xs ys st.mb with
  | some zs =>
    exact Spec.ret' fun hinv env g => (hinv.2 av env g).1 _ xs ys zs (findMB_mem _ xs ys st.mb zs hf)
  | none =>
    dsimp only
    rcases h1 : blastBinRaw op st xs ys with ⟨st1, zs⟩
    have s1 := h1 ▸ blastBinRaw_spec (av := av) op st xs ys
    dsimp only
    have ext2 : Ext st { st1 with mb := (opCode op, xs, ys, zs) :: st1.mb } := by
      refine ⟨s1.1.1, fun hinv => ?_⟩
      have hinv1 := s1.1.2 hinv
      refine ⟨hinv1.1, ?_⟩
      intro av' env g
      obtain ⟨m1, m2⟩ := hinv1.2 av' env g
      refine ⟨fun c' xs' ys' zs' hm => ?_, m2⟩
      rcases List.mem_cons.mp hm with he | he
      · simp only [Prod.mk.injEq] at he
        rw [he.1, he.2.1, he.2.2.1, he.2.2.2]
        exact (h1 ▸ blastBinRaw_spec (av := av') op st xs ys).2 hinv env g
      · exact m1 c' xs' ys' zs' he
    exact ⟨ext2, fun hinv env g => s1.2 hinv env g⟩


end BVS
