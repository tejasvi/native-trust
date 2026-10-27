module

public import BVS.LratBits
public import BVS.LratBitsSound
public import BVS.Lrat.Trie
public import BVS.Sound.Basic

@[expose] public section
/-!
# Chunked LRAT checking over a lookup function

* Each hint names its clause and what it does: `k = 0` conflict (every literal is false),
  `k = 2u+1` the positive literal `u` becomes true, `k = 2u+2` the negative literal `u` becomes
  true. The kernel checks this with subset tests on bitmasks (`land`/`xor`), and hints that do
  nothing are dropped by the (untrusted) annotator.
* The checker is generic in the lookup function (`look`), so the soundness proofs do not depend on
  the store. `ChainL look s e` states that every assignment satisfying the clauses below id `s`
  satisfies those below `e`; chunks compose with `ChainL.trans`.
* The drivers use `chkUR`/`chkUR_sound` (recursor forms, evaluated by the kernel) with the lookup
  `look4` of `BVS.Lrat.LeafTree`. The perfect tree `MT` with its in-order check `agreeM` and the
  checkers `chkU`, `chkL`, `chkLR` are earlier variants of the same design.
-/
namespace BVS
open LratBits

abbrev Clause := List (Nat × Bool)

inductive MT where
  | leaf (v : Option Clause)
  | node (l r : MT)

def MT.get : MT → Nat → Nat → Option Clause
  | .leaf v, _, _ => v
  | .node l r, half, k => cond (Nat.blt k half) (MT.get l (half / 2) k) (MT.get r (half / 2) (k - half))

/-- In-order check of the leaves against `xs` (`none` = no constraint); `d` is the depth. Returns
the rest of `xs`. -/
def agreeM : MT → Nat → List (Option Clause) → Option (List (Option Clause))
  | _, _, [] => some []
  | .leaf v, 0, x :: xs => cond (optOK x v) (some xs) none
  | .leaf _, _ + 1, _ :: _ => none
  | .node _ _, 0, _ :: _ => none
  | .node l r, d + 1, xs =>
    match agreeM l d xs with
    | some ys => agreeM r d ys
    | none => none

theorem optOK_get {x v : Option Clause} {c : Clause} (h : optOK x v = true) (hx : x = some c) :
    v = some c := by
  subst hx
  cases v with
  | none => simp [optOK] at h
  | some d => simp only [optOK] at h; rw [clEq_eq _ _ h]

theorem agreeM_sound : ∀ (t : MT) (d : Nat) (xs ys : List (Option Clause)), agreeM t d xs = some ys →
    (∀ k c, k < 2 ^ d → xs[k]? = some (some c) → t.get (2 ^ d / 2) k = some c) ∧ ys = xs.drop (2 ^ d)
  | t, d, [], ys, h => by
    cases t <;> cases d <;> (simp only [agreeM, Option.some.injEq] at h; subst h; exact ⟨fun k c _ hk => by simp at hk, by simp⟩)
  | .leaf v, 0, x :: xs, ys, h => by
    simp only [agreeM] at h
    cases ho : optOK x v
    · rw [ho] at h; simp [cond] at h
    · rw [ho] at h; simp only [cond, Option.some.injEq] at h; subst h
      refine ⟨fun k c hk hx => ?_, by simp⟩
      have : k = 0 := by simpa using hk
      subst this
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      exact optOK_get ho hx
  | .leaf v, d + 1, x :: xs, ys, h => by simp [agreeM] at h
  | .node l r, 0, x :: xs, ys, h => by simp [agreeM] at h
  | .node l r, d + 1, x :: xs', ys, h => by
    simp only [agreeM] at h
    generalize hxs : x :: xs' = xs at h ⊢
    cases h1 : agreeM l d xs with
    | none => rw [h1] at h; simp at h
    | some ys1 =>
      rw [h1] at h; simp only at h
      obtain ⟨hl, e1⟩ := agreeM_sound l d xs ys1 h1
      obtain ⟨hr, e2⟩ := agreeM_sound r d ys1 ys h
      have hp : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; omega
      refine ⟨fun k c hk hx => ?_, by rw [e2, e1, List.drop_drop, Nat.pow_succ]; congr 1; omega⟩
      simp only [MT.get, hp, nat_blt_eq, cond_decide]
      by_cases hkd : k < 2 ^ d
      · rw [if_pos hkd]; exact hl k c hkd hx
      · rw [if_neg hkd]
        apply hr (k - 2 ^ d) c (by rw [Nat.pow_succ] at hk; omega)
        rw [e1, List.getElem?_drop, show 2 ^ d + (k - 2 ^ d) = k by omega]; exact hx

/-! ## The checker, generic in the lookup -/

/-- Unit propagation with annotated hints `(clause id, k)`. -/
def propU (look : Nat → Option Clause) (id : Nat) : Nat → Nat → List (Nat × Nat) → Bool
  | _, _, [] => false
  | pa, na, (h, k) :: hs =>
    cond (Nat.ble 1 h && Nat.blt h id)
      (match look h with
       | none => false
       | some c =>
         match litsBits c 0 0 with
         | (cp, cn) =>
           cond (Nat.beq k 0)
             (Nat.beq (Nat.land cp na) cp && Nat.beq (Nat.land cn pa) cn)
             (cond (Nat.beq (Nat.mod k 2) 1)
               (cond (Nat.beq (Nat.land (Nat.xor cp (Nat.shiftLeft 1 (Nat.div k 2))) na)
                        (Nat.xor cp (Nat.shiftLeft 1 (Nat.div k 2))) &&
                      Nat.beq (Nat.land cn pa) cn)
                 (propU look id (Nat.lor pa (Nat.shiftLeft 1 (Nat.div k 2))) na hs) false)
               (cond (Nat.beq (Nat.land cp na) cp &&
                      Nat.beq (Nat.land (Nat.xor cn (Nat.shiftLeft 1 (Nat.div k 2 - 1))) pa)
                        (Nat.xor cn (Nat.shiftLeft 1 (Nat.div k 2 - 1))))
                 (propU look id pa (Nat.lor na (Nat.shiftLeft 1 (Nat.div k 2 - 1))) hs) false)))
      false

def stepOkU (look : Nat → Option Clause) (id : Nat) (hints : List (Nat × Nat)) : Bool :=
  match look id with
  | none => false
  | some c =>
    match litsBits c 0 0 with
    | (cp, cn) => cond (Nat.beq (Nat.land cp cn) 0) (propU look id cn cp hints) true

def chkU (look : Nat → Option Clause) : Nat → List (List (Nat × Nat)) → Bool
  | _, [] => true
  | id, hs :: rest => stepOkU look id hs && chkU look (id + 1) rest

def SatBelowL (a : Nat → Bool) (look : Nat → Option Clause) (n : Nat) : Prop :=
  ∀ i c, 1 ≤ i → i < n → look i = some c → ClauseTrue a c

def ChainL (look : Nat → Option Clause) (s e : Nat) : Prop :=
  ∀ a, SatBelowL a look s → SatBelowL a look e

theorem ChainL.trans {look : Nat → Option Clause} {s m e : Nat} (h1 : ChainL look s m) (h2 : ChainL look m e) :
    ChainL look s e := fun a h => h2 a (h1 a h)

theorem subset_of_land {x y : Nat} (h : Nat.beq (Nat.land x y) x = true) (v : Nat) (hv : x.testBit v = true) :
    y.testBit v = true := by
  have e := Nat.eq_of_beq_eq_true h
  have : (Nat.land x y).testBit v = x.testBit v := by rw [e]
  rw [show Nat.land x y = x &&& y from rfl, Nat.testBit_and, hv] at this
  simpa using this

theorem testBit_xor_one_shiftLeft (x u v : Nat) (h : v ≠ u) :
    (Nat.xor x (Nat.shiftLeft 1 u)).testBit v = x.testBit v := by
  rw [show Nat.xor x (Nat.shiftLeft 1 u) = x ^^^ (1 <<< u) from rfl, Nat.testBit_xor, testBit_one_shiftLeft]
  simp [Ne.symm h]

theorem propU_sound {a : Nat → Bool} {look : Nat → Option Clause} {id : Nat} (hT : SatBelowL a look id) :
    ∀ (hints : List (Nat × Nat)) (pa na : Nat), propU look id pa na hints = true → Cons a pa na → False := by
  intro hints
  induction hints with
  | nil => intro pa na h _; exact absurd h (by simp [propU])
  | cons hk hs ih =>
    obtain ⟨h, k⟩ := hk
    intro pa na hp hc
    unfold propU at hp
    cases hb : (Nat.ble 1 h && Nat.blt h id)
    · rw [hb] at hp; exact absurd hp (by simp)
    · rw [hb] at hp
      simp only [cond] at hp
      have hb' : 1 ≤ h ∧ h < id := by
        simp only [Bool.and_eq_true] at hb
        exact ⟨Nat.le_of_ble_eq_true hb.1, by
          have := hb.2; unfold Nat.blt at this; exact Nat.le_of_ble_eq_true this⟩
      cases hg : look h with
      | none => rw [hg] at hp; exact absurd hp (by simp)
      | some cc =>
        rw [hg] at hp
        dsimp only at hp
        have hsat := bsat_of_clauseTrue (hT h cc hb'.1 hb'.2 hg)
        generalize litsBits cc 0 0 = q at hsat hp
        obtain ⟨cp, cn⟩ := q
        dsimp only at hp
        obtain ⟨w, hw⟩ := hsat
        -- facts from the assignment
        have hpa : ∀ v, pa.testBit v = true → a v = true := fun v hv => (hc v).1 hv
        have hna : ∀ v, na.testBit v = true → a v = false := fun v hv => (hc v).2 hv
        cases hk0 : Nat.beq k 0
        · rw [hk0] at hp; simp only [cond] at hp
          cases hk1 : Nat.beq (Nat.mod k 2) 1
          · -- negative unit `u = k / 2 - 1`
            rw [hk1] at hp; simp only [cond] at hp
            generalize hu : Nat.div k 2 - 1 = u at hp
            cases hchk : (Nat.beq (Nat.land cp na) cp &&
                Nat.beq (Nat.land (Nat.xor cn (Nat.shiftLeft 1 u)) pa) (Nat.xor cn (Nat.shiftLeft 1 u)))
            · rw [hchk] at hp; exact absurd hp (by simp)
            · rw [hchk] at hp; simp only [cond] at hp
              simp only [Bool.and_eq_true] at hchk
              -- the literal `¬u` is true under `a`
              have key : a u = false := by
                rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · rw [hna w (subset_of_land hchk.1 w h1)] at h2; exact absurd h2 (by simp)
                · by_cases hwu : w = u
                  · subst hwu; exact h2
                  · have := subset_of_land hchk.2 w (by rw [testBit_xor_one_shiftLeft _ _ _ hwu]; exact h1)
                    rw [hpa w this] at h2; exact absurd h2 (by simp)
              apply ih pa (Nat.lor na (Nat.shiftLeft 1 u)) hp
              intro v
              refine ⟨fun hv => hpa v hv, fun hv => ?_⟩
              rw [show Nat.lor na (Nat.shiftLeft 1 u) = na ||| (1 <<< u) from rfl, Nat.testBit_or,
                testBit_one_shiftLeft] at hv
              cases hnv : na.testBit v
              · rw [hnv, Bool.false_or] at hv; rw [← of_decide_eq_true hv]; exact key
              · exact hna v hnv
          · -- positive unit `u = k / 2`
            rw [hk1] at hp; simp only [cond] at hp
            generalize hu : Nat.div k 2 = u at hp
            cases hchk : (Nat.beq (Nat.land (Nat.xor cp (Nat.shiftLeft 1 u)) na) (Nat.xor cp (Nat.shiftLeft 1 u)) &&
                Nat.beq (Nat.land cn pa) cn)
            · rw [hchk] at hp; exact absurd hp (by simp)
            · rw [hchk] at hp; simp only [cond] at hp
              simp only [Bool.and_eq_true] at hchk
              have key : a u = true := by
                rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
                · by_cases hwu : w = u
                  · subst hwu; exact h2
                  · have := subset_of_land hchk.1 w (by rw [testBit_xor_one_shiftLeft _ _ _ hwu]; exact h1)
                    rw [hna w this] at h2; exact absurd h2 (by simp)
                · rw [hpa w (subset_of_land hchk.2 w h1)] at h2; exact absurd h2 (by simp)
              apply ih (Nat.lor pa (Nat.shiftLeft 1 u)) na hp
              intro v
              refine ⟨fun hv => ?_, fun hv => hna v hv⟩
              rw [show Nat.lor pa (Nat.shiftLeft 1 u) = pa ||| (1 <<< u) from rfl, Nat.testBit_or,
                testBit_one_shiftLeft] at hv
              cases hpv : pa.testBit v
              · rw [hpv, Bool.false_or] at hv; rw [← of_decide_eq_true hv]; exact key
              · exact hpa v hpv
        · -- conflict
          rw [hk0] at hp; simp only [cond, Bool.and_eq_true] at hp
          rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
          · rw [hna w (subset_of_land hp.1 w h1)] at h2; exact absurd h2 (by simp)
          · rw [hpa w (subset_of_land hp.2 w h1)] at h2; exact absurd h2 (by simp)

theorem stepOkU_sound {a : Nat → Bool} {look : Nat → Option Clause} {id : Nat} {hints : List (Nat × Nat)}
    (hT : SatBelowL a look id) (h : stepOkU look id hints = true) : ∀ c, look id = some c → ClauseTrue a c := by
  intro c hc
  unfold stepOkU at h
  rw [hc] at h
  dsimp only at h
  apply clauseTrue_of_bsat
  generalize litsBits c 0 0 = q at h ⊢
  obtain ⟨cp, cn⟩ := q
  dsimp only at h
  cases hb : Nat.beq (Nat.land cp cn) 0
  · have hne : cp &&& cn ≠ 0 := by
      intro h0; rw [show Nat.land cp cn = cp &&& cn from rfl, h0] at hb; exact absurd hb (by decide)
    obtain ⟨v, hv⟩ := Nat.exists_testBit_of_ne_zero hne
    rw [Nat.testBit_and] at hv
    cases h1 : cp.testBit v <;> cases h2 : cn.testBit v <;> rw [h1, h2] at hv
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · cases hav : a v
      · exact ⟨v, Or.inr ⟨h2, hav⟩⟩
      · exact ⟨v, Or.inl ⟨h1, hav⟩⟩
  · rw [hb] at h
    simp only [cond] at h
    apply Classical.byContradiction
    intro hns
    apply propU_sound hT hints cn cp h
    intro v
    constructor
    · intro hv
      cases hav : a v
      · exact absurd ⟨v, Or.inr ⟨hv, hav⟩⟩ hns
      · rfl
    · intro hv
      cases hav : a v
      · rfl
      · exact absurd ⟨v, Or.inl ⟨hv, hav⟩⟩ hns

theorem chkU_sound (look : Nat → Option Clause) : ∀ (steps : List (List (Nat × Nat))) (id : Nat),
    chkU look id steps = true → ChainL look id (id + steps.length)
  | [], id, _ => fun a h => by simpa using h
  | hs :: rest, id, h => by
    simp only [chkU, Bool.and_eq_true] at h
    intro a hT
    have h1 : SatBelowL a look (id + 1) := by
      intro i c hi1 hi2 hc
      by_cases hi : i < id
      · exact hT i c hi1 hi hc
      · have : i = id := by omega
        subst this
        exact stepOkU_sound hT h.1 c hc
    have := chkU_sound look rest (id + 1) h.2 a h1
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

/-! ## Recursor forms for the kernel -/

noncomputable def MT.getR (t : MT) : Nat → Nat → Option Clause :=
  MT.rec (motive := fun _ => Nat → Nat → Option Clause) (fun v _ _ => v)
    (fun _ _ ihl ihr half k => Bool.casesOn (motive := fun _ => Option Clause) (Nat.blt k half)
      (ihr (Nat.div half 2) (Nat.sub k half)) (ihl (Nat.div half 2) k)) t

theorem MT.getR_eq : ∀ (t : MT) (half k : Nat), t.getR half k = t.get half k
  | .leaf v, _, _ => rfl
  | .node l r, half, k => by
    show Bool.casesOn (motive := fun _ => Option Clause) (Nat.blt k half)
      (r.getR (Nat.div half 2) (Nat.sub k half)) (l.getR (Nat.div half 2) k) = MT.get (.node l r) half k
    rw [MT.getR_eq l, MT.getR_eq r]
    show _ = cond (Nat.blt k half) (l.get (half / 2) k) (r.get (half / 2) (k - half))
    cases Nat.blt k half <;> rfl

/-! ## The `LratBits.step` checker over a lookup, with recursor forms

The same propagation as `propT` (one bitmask step per hint, unit variable named by the hint), over
an arbitrary lookup function. -/

def propL (look : Nat → Option Clause) (id : Nat) : Nat → Nat → List (Nat × Nat) → Bool
  | _, _, [] => false
  | pa, na, (h, u) :: hs =>
    cond (Nat.ble 1 h && Nat.blt h id)
      (match look h with
       | none => false
       | some c =>
         match litsBits c 0 0 with
         | (cp, cn) =>
           match step cp cn pa na u with
           | .conflict => true
           | .unit pa' na' => propL look id pa' na' hs
           | .skip => propL look id pa na hs)
      false

def stepOkL (look : Nat → Option Clause) (id : Nat) (hints : List (Nat × Nat)) : Bool :=
  match look id with
  | none => false
  | some c =>
    match litsBits c 0 0 with
    | (cp, cn) => cond (Nat.beq (cp &&& cn) 0) (propL look id cn cp hints) true

def chkL (look : Nat → Option Clause) : Nat → List (List (Nat × Nat)) → Bool
  | _, [] => true
  | id, hs :: rest => stepOkL look id hs && chkL look (id + 1) rest

theorem propL_sound {a : Nat → Bool} {look : Nat → Option Clause} {id : Nat} (hT : SatBelowL a look id) :
    ∀ (hints : List (Nat × Nat)) (pa na : Nat), propL look id pa na hints = true → Cons a pa na → False := by
  intro hints
  induction hints with
  | nil => intro pa na h _; exact absurd h (by simp [propL])
  | cons hu hs ih =>
    obtain ⟨h, u⟩ := hu
    intro pa na hp hc
    unfold propL at hp
    cases hb : (Nat.ble 1 h && Nat.blt h id)
    · rw [hb] at hp; exact absurd hp (by simp)
    · rw [hb] at hp
      simp only [cond] at hp
      have hb' : 1 ≤ h ∧ h < id := by
        simp only [Bool.and_eq_true] at hb
        exact ⟨Nat.le_of_ble_eq_true hb.1, by
          have := hb.2; unfold Nat.blt at this; exact Nat.le_of_ble_eq_true this⟩
      cases hg : look h with
      | none => rw [hg] at hp; exact absurd hp (by simp)
      | some cc =>
        rw [hg] at hp
        dsimp only at hp
        have hsat := bsat_of_clauseTrue (hT h cc hb'.1 hb'.2 hg)
        generalize litsBits cc 0 0 = q at hsat hp
        obtain ⟨cp, cn⟩ := q
        dsimp only at hp
        have hspec := step_spec (u := u) hsat hc
        revert hp hspec
        cases step cp cn pa na u with
        | conflict => intro _ hspec; exact hspec
        | unit pa' na' => intro hp hspec; exact ih pa' na' hp hspec
        | skip => intro hp _; exact ih pa na hp hc

theorem stepOkL_sound {a : Nat → Bool} {look : Nat → Option Clause} {id : Nat} {hints : List (Nat × Nat)}
    (hT : SatBelowL a look id) (h : stepOkL look id hints = true) : ∀ c, look id = some c → ClauseTrue a c := by
  intro c hc
  unfold stepOkL at h
  rw [hc] at h
  dsimp only at h
  apply clauseTrue_of_bsat
  generalize litsBits c 0 0 = q at h ⊢
  obtain ⟨cp, cn⟩ := q
  dsimp only at h
  cases hb : Nat.beq (cp &&& cn) 0
  · have hne : cp &&& cn ≠ 0 := by
      intro h0; rw [h0] at hb; exact absurd hb (by decide)
    obtain ⟨v, hv⟩ := Nat.exists_testBit_of_ne_zero hne
    rw [Nat.testBit_and] at hv
    cases h1 : cp.testBit v <;> cases h2 : cn.testBit v <;> rw [h1, h2] at hv
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · exact absurd hv (by decide)
    · cases hav : a v
      · exact ⟨v, Or.inr ⟨h2, hav⟩⟩
      · exact ⟨v, Or.inl ⟨h1, hav⟩⟩
  · rw [hb] at h
    simp only [cond] at h
    apply Classical.byContradiction
    intro hns
    apply propL_sound hT hints cn cp h
    intro v
    constructor
    · intro hv
      cases hav : a v
      · exact absurd ⟨v, Or.inr ⟨hv, hav⟩⟩ hns
      · rfl
    · intro hv
      cases hav : a v
      · rfl
      · exact absurd ⟨v, Or.inl ⟨hv, hav⟩⟩ hns

theorem chkL_sound (look : Nat → Option Clause) : ∀ (steps : List (List (Nat × Nat))) (id : Nat),
    chkL look id steps = true → ChainL look id (id + steps.length)
  | [], id, _ => fun a h => by simpa using h
  | hs :: rest, id, h => by
    simp only [chkL, Bool.and_eq_true] at h
    intro a hT
    have h1 : SatBelowL a look (id + 1) := by
      intro i c hi1 hi2 hc
      by_cases hi : i < id
      · exact hT i c hi1 hi hc
      · have : i = id := by omega
        subst this
        exact stepOkL_sound hT h.1 c hc
    have := chkL_sound look rest (id + 1) h.2 a h1
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

noncomputable def propLR (look : Nat → Option Clause) (id : Nat) (hs : List (Nat × Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun hu _ ih pa na => Prod.casesOn (motive := fun _ => Bool) hu fun h u =>
      cond (Nat.ble 1 h && Nat.ble (Nat.succ h) id)
        (Option.casesOn (motive := fun _ => Bool) (look h) false fun c =>
          Prod.casesOn (motive := fun _ => Bool) (litsBits c 0 0) fun cp cn =>
            Step.casesOn (motive := fun _ => Bool) (stepK cp cn pa na u) true
              (fun pa' na' => ih pa' na') (ih pa na))
        false) hs

theorem propLR_eq (look : Nat → Option Clause) (id : Nat) : ∀ (hs : List (Nat × Nat)) (pa na : Nat),
    propLR look id hs pa na = propL look id pa na hs
  | [], _, _ => rfl
  | (h, u) :: hs, pa, na => by
    unfold propLR
    dsimp only
    rw [stepK_eq]
    simp only [propL]
    have hb : Nat.ble (Nat.succ h) id = Nat.blt h id := rfl
    rw [hb]
    cases Nat.ble 1 h && Nat.blt h id
    · rfl
    · simp only [cond]
      cases look h with
      | none => rfl
      | some c =>
        dsimp only
        cases litsBits c 0 0 with
        | mk cp cn =>
          dsimp only
          cases step cp cn pa na u with
          | conflict => rfl
          | unit pa' na' => exact propLR_eq look id hs pa' na'
          | skip => exact propLR_eq look id hs pa na

noncomputable def stepOkLR (look : Nat → Option Clause) (id : Nat) (hints : List (Nat × Nat)) : Bool :=
  Option.casesOn (motive := fun _ => Bool) (look id) false fun c =>
    Prod.casesOn (motive := fun _ => Bool) (litsBits c 0 0) fun cp cn =>
      cond (Nat.beq (Nat.land cp cn) 0) (propLR look id hints cn cp) true

theorem stepOkLR_eq (look : Nat → Option Clause) (id : Nat) (hints : List (Nat × Nat)) :
    stepOkLR look id hints = stepOkL look id hints := by
  unfold stepOkLR stepOkL
  cases look id with
  | none => rfl
  | some c =>
    dsimp only
    cases litsBits c 0 0 with
    | mk cp cn =>
      dsimp only
      rw [propLR_eq]; rfl

/-- The form the driver gives to the kernel. -/
noncomputable def chkLR (look : Nat → Option Clause) (id : Nat) (steps : List (List (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun hs _ ih id => stepOkLR look id hs && ih (Nat.succ id)) steps id

theorem chkLR_eq (look : Nat → Option Clause) : ∀ (steps : List (List (Nat × Nat))) (id : Nat),
    chkLR look id steps = chkL look id steps
  | [], _ => rfl
  | hs :: rest, id => by
    show (stepOkLR look id hs && chkLR look (Nat.succ id) rest) = chkL look id (hs :: rest)
    rw [stepOkLR_eq, chkLR_eq look rest]; rfl

theorem chkLR_sound (look : Nat → Option Clause) (steps : List (List (Nat × Nat))) (id : Nat)
    (h : chkLR look id steps = true) : ChainL look id (id + steps.length) :=
  chkL_sound look steps id (by rw [← chkLR_eq]; exact h)

/-! ## Annotated hints in recursor form -/

noncomputable def propUR (look : Nat → Option Clause) (id : Nat) (hs : List (Nat × Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun hk _ ih pa na =>
      cond (Nat.ble 1 hk.1 && Nat.ble (Nat.succ hk.1) id)
        (Option.casesOn (motive := fun _ => Bool) (look hk.1) false fun c =>
          cond (Nat.beq hk.2 0)
            (Nat.beq (Nat.land (litsBits c 0 0).1 na) (litsBits c 0 0).1 &&
              Nat.beq (Nat.land (litsBits c 0 0).2 pa) (litsBits c 0 0).2)
            (cond (Nat.beq (Nat.mod hk.2 2) 1)
              (cond (Nat.beq (Nat.land (Nat.xor (litsBits c 0 0).1 (Nat.shiftLeft 1 (Nat.div hk.2 2))) na)
                       (Nat.xor (litsBits c 0 0).1 (Nat.shiftLeft 1 (Nat.div hk.2 2))) &&
                     Nat.beq (Nat.land (litsBits c 0 0).2 pa) (litsBits c 0 0).2)
                (ih (Nat.lor pa (Nat.shiftLeft 1 (Nat.div hk.2 2))) na) false)
              (cond (Nat.beq (Nat.land (litsBits c 0 0).1 na) (litsBits c 0 0).1 &&
                     Nat.beq (Nat.land (Nat.xor (litsBits c 0 0).2 (Nat.shiftLeft 1 (Nat.div hk.2 2 - 1))) pa)
                       (Nat.xor (litsBits c 0 0).2 (Nat.shiftLeft 1 (Nat.div hk.2 2 - 1))))
                (ih pa (Nat.lor na (Nat.shiftLeft 1 (Nat.div hk.2 2 - 1)))) false)))
        false) hs

theorem propUR_eq (look : Nat → Option Clause) (id : Nat) : ∀ (hs : List (Nat × Nat)) (pa na : Nat),
    propUR look id hs pa na = propU look id pa na hs
  | [], _, _ => rfl
  | (h, k) :: hs, pa, na => by
    have ih := propUR_eq look id hs
    unfold propUR
    dsimp only
    simp only [propU]
    have hb : Nat.ble (Nat.succ h) id = Nat.blt h id := rfl
    rw [hb]
    cases Nat.ble 1 h && Nat.blt h id
    · rfl
    · simp only [cond]
      cases look h with
      | none => rfl
      | some c =>
        dsimp only
        cases litsBits c 0 0 with
        | mk cp cn =>
          dsimp only
          cases Nat.beq k 0
          · simp only [cond]
            cases Nat.beq (Nat.mod k 2) 1
            · simp only [cond]
              cases (Nat.beq (Nat.land cp na) cp &&
                  Nat.beq (Nat.land (Nat.xor cn (Nat.shiftLeft 1 (Nat.div k 2 - 1))) pa)
                    (Nat.xor cn (Nat.shiftLeft 1 (Nat.div k 2 - 1))))
              · rfl
              · exact ih _ _
            · simp only [cond]
              cases (Nat.beq (Nat.land (Nat.xor cp (Nat.shiftLeft 1 (Nat.div k 2))) na)
                    (Nat.xor cp (Nat.shiftLeft 1 (Nat.div k 2))) && Nat.beq (Nat.land cn pa) cn)
              · rfl
              · exact ih _ _
          · rfl

noncomputable def stepOkUR (look : Nat → Option Clause) (id : Nat) (hints : List (Nat × Nat)) : Bool :=
  Option.casesOn (motive := fun _ => Bool) (look id) false fun c =>
    cond (Nat.beq (Nat.land (litsBits c 0 0).1 (litsBits c 0 0).2) 0)
      (propUR look id hints (litsBits c 0 0).2 (litsBits c 0 0).1) true

theorem stepOkUR_eq (look : Nat → Option Clause) (id : Nat) (hints : List (Nat × Nat)) :
    stepOkUR look id hints = stepOkU look id hints := by
  unfold stepOkUR stepOkU
  cases look id with
  | none => rfl
  | some c =>
    dsimp only
    cases litsBits c 0 0 with
    | mk cp cn =>
      dsimp only
      rw [propUR_eq]

noncomputable def chkUR (look : Nat → Option Clause) (id : Nat) (steps : List (List (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun hs _ ih id => stepOkUR look id hs && ih (Nat.succ id)) steps id

theorem chkUR_eq (look : Nat → Option Clause) : ∀ (steps : List (List (Nat × Nat))) (id : Nat),
    chkUR look id steps = chkU look id steps
  | [], _ => rfl
  | hs :: rest, id => by
    show (stepOkUR look id hs && chkUR look (Nat.succ id) rest) = chkU look id (hs :: rest)
    rw [stepOkUR_eq, chkUR_eq look rest]; rfl

theorem chkUR_sound (look : Nat → Option Clause) (steps : List (List (Nat × Nat))) (id : Nat)
    (h : chkUR look id steps = true) : ChainL look id (id + steps.length) :=
  chkU_sound look steps id (by rw [← chkUR_eq]; exact h)

end BVS
