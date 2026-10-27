module

public import BVS.LratBits
public import BVS.LratBitsSound
public import BVS.Blast

@[expose] public section
/-!
# Clause equality and a first chunked LRAT checker over a fixed clause trie

The drivers of this package use `clEq`/`clEq_eq` from this module (in `BVS.Lrat.LeafTree`); their
LRAT checker is `chkUR` in `BVS.Lrat.Chain`. The checker below is the first version of the same idea.

The certificate is untrusted data: a clause trie `T : CT` holding the original clauses at ids
`1 … |F|` and the learned clauses after them, and for every learned clause its hints (each with the
variable it makes unit). Because `T` is a fixed term, the kernel's evaluation cache memoizes every
lookup and every clause-to-bitmask conversion across steps, and the steps can be split over many
declarations (`chkChunk`), each one proving `ChainOK T s e`: clauses below `e` follow from clauses
below `s`.

* `agree T F 1` checks that `T` holds the CNF `F` at ids `1 … |F|`;
* `chkChunk T s steps` checks the clauses at ids `s, s+1, …` by reverse unit propagation, using
  only clauses with smaller ids (`LratBits.step` on bitmasks);
* `unsat_of_agree`: `agree`, a chain from `|F| + 1` to `N + 1`, and the empty clause at id `N` give
  the unsatisfiability of `F`.
-/
namespace BVS
open LratBits

/-- The clause store: clause id ↦ clause (CNF literals `(variable, polarity)`). -/
abbrev CT := NT (List (Nat × Bool))

def litEq (a b : Nat × Bool) : Bool := Nat.beq a.1 b.1 && (a.2 == b.2)

def clEq : List (Nat × Bool) → List (Nat × Bool) → Bool
  | [], [] => true
  | a :: as, b :: bs => litEq a b && clEq as bs
  | _, _ => false

/-- `T` holds the clauses of `F` at ids `i, i+1, …`. -/
def agree (T : CT) : List (List (Nat × Bool)) → Nat → Bool
  | [], _ => true
  | c :: cs, i => (match T.get i with | some d => clEq c d | none => false) && agree T cs (i + 1)

/-- Unit propagation along the hints `(clause id, unit variable)`; hints must be below `id`. -/
def propT (T : CT) (id : Nat) : Nat → Nat → List (Nat × Nat) → Bool
  | _, _, [] => false
  | pa, na, (h, u) :: hs =>
    cond (Nat.ble 1 h && Nat.blt h id)
      (match T.get h with
       | none => false
       | some c =>
         match litsBits c 0 0 with
         | (cp, cn) =>
           match step cp cn pa na u with
           | .conflict => true
           | .unit pa' na' => propT T id pa' na' hs
           | .skip => propT T id pa na hs)
      false

/-- The clause at id `id` is a tautology or follows by unit propagation. -/
def stepOk (T : CT) (id : Nat) (hints : List (Nat × Nat)) : Bool :=
  match T.get id with
  | none => false
  | some c =>
    match litsBits c 0 0 with
    | (cp, cn) => cond (Nat.beq (cp &&& cn) 0) (propT T id cn cp hints) true

/-- Check the clauses at ids `id, id+1, …` (one hint list each). -/
def chkChunk (T : CT) : Nat → List (List (Nat × Nat)) → Bool
  | _, [] => true
  | id, hs :: rest => stepOk T id hs && chkChunk T (id + 1) rest

/-! ## Soundness -/

/-- Every clause of `T` with id in `[1, n)` is true under `a`. -/
def SatBelow (a : Nat → Bool) (T : CT) (n : Nat) : Prop :=
  ∀ i c, 1 ≤ i → i < n → T.get i = some c → ClauseTrue a c

/-- Clauses below `e` follow from clauses below `s`. -/
def ChainOK (T : CT) (s e : Nat) : Prop := ∀ a, SatBelow a T s → SatBelow a T e

theorem ChainOK.trans {T : CT} {s m e : Nat} (h1 : ChainOK T s m) (h2 : ChainOK T m e) : ChainOK T s e :=
  fun a h => h2 a (h1 a h)

theorem litsBits_mem : ∀ (c : List (Nat × Bool)) (cp cn v : Nat),
    ((litsBits c cp cn).1.testBit v = true → cp.testBit v = true ∨ (v, true) ∈ c) ∧
    ((litsBits c cp cn).2.testBit v = true → cn.testBit v = true ∨ (v, false) ∈ c)
  | [], cp, cn, v => ⟨fun h => Or.inl h, fun h => Or.inl h⟩
  | (w, b) :: l, cp, cn, v => by
    cases b with
    | true =>
      have ih := litsBits_mem l (cp ||| (1 <<< w)) cn v
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases ih.1 h with h' | h'
        · rw [Nat.testBit_or, testBit_one_shiftLeft] at h'
          cases hc : cp.testBit v
          · rw [hc, Bool.false_or] at h'
            right; rw [← of_decide_eq_true h']; exact List.mem_cons_self ..
          · left; rfl
        · right; exact List.mem_cons_of_mem _ h'
      · rcases ih.2 h with h' | h'
        · left; exact h'
        · right; exact List.mem_cons_of_mem _ h'
    | false =>
      have ih := litsBits_mem l cp (cn ||| (1 <<< w)) v
      refine ⟨fun h => ?_, fun h => ?_⟩
      · rcases ih.1 h with h' | h'
        · left; exact h'
        · right; exact List.mem_cons_of_mem _ h'
      · rcases ih.2 h with h' | h'
        · rw [Nat.testBit_or, testBit_one_shiftLeft] at h'
          cases hc : cn.testBit v
          · rw [hc, Bool.false_or] at h'
            right; rw [← of_decide_eq_true h']; exact List.mem_cons_self ..
          · left; rfl
        · right; exact List.mem_cons_of_mem _ h'

theorem clauseTrue_of_bsat {a : Nat → Bool} {c : List (Nat × Bool)} (h : BSat a (litsBits c 0 0)) :
    ClauseTrue a c := by
  obtain ⟨v, hv⟩ := h
  unfold ClauseTrue
  rw [List.any_eq_true]
  rcases hv with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · rcases (litsBits_mem c 0 0 v).1 h1 with h' | h'
    · rw [Nat.zero_testBit] at h'; exact absurd h' (by simp)
    · exact ⟨_, h', by simp [h2]⟩
  · rcases (litsBits_mem c 0 0 v).2 h1 with h' | h'
    · rw [Nat.zero_testBit] at h'; exact absurd h' (by simp)
    · exact ⟨_, h', by simp [h2]⟩

theorem bsat_of_clauseTrue {a : Nat → Bool} {c : List (Nat × Bool)} (h : ClauseTrue a c) :
    BSat a (litsBits c 0 0) :=
  litsBits_sat c 0 0 (Or.inl h)

theorem propT_sound {a : Nat → Bool} {T : CT} {id : Nat} (hT : SatBelow a T id) :
    ∀ (hints : List (Nat × Nat)) (pa na : Nat), propT T id pa na hints = true → Cons a pa na → False := by
  intro hints
  induction hints with
  | nil => intro pa na h _; exact absurd h (by simp [propT])
  | cons hu hs ih =>
    obtain ⟨h, u⟩ := hu
    intro pa na hp hc
    unfold propT at hp
    cases hb : (Nat.ble 1 h && Nat.blt h id)
    · rw [hb] at hp; exact absurd hp (by simp)
    · rw [hb] at hp
      simp only [cond] at hp
      have hb' : 1 ≤ h ∧ h < id := by
        simp only [Bool.and_eq_true] at hb
        exact ⟨Nat.le_of_ble_eq_true hb.1, by
          have := hb.2; unfold Nat.blt at this; exact Nat.le_of_ble_eq_true this⟩
      cases hg : T.get h with
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

theorem stepOk_sound {a : Nat → Bool} {T : CT} {id : Nat} {hints : List (Nat × Nat)}
    (hT : SatBelow a T id) (h : stepOk T id hints = true) : ∀ c, T.get id = some c → ClauseTrue a c := by
  intro c hc
  unfold stepOk at h
  rw [hc] at h
  dsimp only at h
  apply clauseTrue_of_bsat
  generalize litsBits c 0 0 = q at h ⊢
  obtain ⟨cp, cn⟩ := q
  dsimp only at h
  cases hb : Nat.beq (cp &&& cn) 0
  · -- a tautology
    have hne : cp &&& cn ≠ 0 := by
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
    apply propT_sound hT hints cn cp h
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

theorem chkChunk_sound (T : CT) : ∀ (steps : List (List (Nat × Nat))) (id : Nat),
    chkChunk T id steps = true → ChainOK T id (id + steps.length)
  | [], id, _ => fun a h => by simpa using h
  | hs :: rest, id, h => by
    simp only [chkChunk, Bool.and_eq_true] at h
    intro a hT
    have h1 : SatBelow a T (id + 1) := by
      intro i c hi1 hi2 hc
      by_cases hi : i < id
      · exact hT i c hi1 hi hc
      · have : i = id := by omega
        subst this
        exact stepOk_sound hT h.1 c hc
    have := chkChunk_sound T rest (id + 1) h.2 a h1
    simpa [Nat.add_assoc, Nat.add_comm 1] using this

theorem clEq_eq : ∀ (c d : List (Nat × Bool)), clEq c d = true → c = d
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [clEq, Bool.and_eq_true, litEq] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    have e1 := Nat.eq_of_beq_eq_true h1
    have e2 : a.2 = b.2 := by simpa using h2
    rw [clEq_eq as bs h3]
    obtain ⟨a1, a2⟩ := a; obtain ⟨b1, b2⟩ := b
    simp only at e1 e2; subst e1; subst e2; rfl
  | [], _ :: _, h => by simp [clEq] at h
  | _ :: _, [], h => by simp [clEq] at h

theorem agree_sound (T : CT) (a : Nat → Bool) : ∀ (F : List (List (Nat × Bool))) (i : Nat),
    agree T F i = true → F.all (fun c => c.any (fun l => a l.1 == l.2)) = true →
    ∀ k c, i ≤ k → k < i + F.length → T.get k = some c → ClauseTrue a c
  | [], i, _, _, k, c, h1, h2, _ => by simp at h2; omega
  | d :: ds, i, h, hF, k, c, h1, h2, hk => by
    simp only [agree, Bool.and_eq_true] at h
    simp only [List.all_cons, Bool.and_eq_true] at hF
    by_cases hki : k = i
    · subst hki
      rw [hk] at h
      have := clEq_eq _ _ h.1
      subst this
      exact hF.1
    · exact agree_sound T a ds (i + 1) h.2 hF.2 k c (by omega) (by simp at h2; omega) hk

/-- **Soundness of the chunked checker.** -/
theorem unsat_of_agree (F : List (List (Nat × Bool))) (T : CT) (N : Nat)
    (hag : agree T F 1 = true) (hch : ChainOK T (F.length + 1) (N + 1)) (hN1 : 1 ≤ N)
    (hN : T.get N = some []) :
    ∀ a : Nat → Bool, F.all (fun c => c.any (fun l => a l.1 == l.2)) = false := by
  intro a
  cases hF : F.all (fun c => c.any (fun l => a l.1 == l.2))
  · rfl
  · exfalso
    have h0 : SatBelow a T (F.length + 1) := fun k c h1 h2 hk =>
      agree_sound T a F 1 hag hF k c h1 (by omega) hk
    have := hch a h0 N [] hN1 (by omega) hN
    simp [ClauseTrue] at this

/-! ## Faster forms for the kernel

`agreeT` checks the original clauses in one traversal of the trie (the list of expected clauses,
indexed by key, is split into odd and even positions along the trie's left/right subtrees), and
`chkR` is `chkChunk` written with recursors and `Nat` primitives (`chkR_eq`). -/

def splitP {α : Type} : List α → List α × List α
  | [] => ([], [])
  | x :: xs => (x :: (splitP xs).2, (splitP xs).1)

theorem splitP_get {α : Type} : ∀ (l : List α) (j : Nat),
    (splitP l).1[j]? = l[2 * j]? ∧ (splitP l).2[j]? = l[2 * j + 1]?
  | [], j => by simp [splitP]
  | x :: xs, j => by
    constructor
    · cases j with
      | zero => simp [splitP]
      | succ j =>
        simp only [splitP, List.getElem?_cons_succ]
        rw [(splitP_get xs j).2]
        rw [show 2 * (j + 1) = (2 * j + 1) + 1 by omega, List.getElem?_cons_succ]
    · simp only [splitP]
      rw [(splitP_get xs j).1, show 2 * j + 1 = (2 * j) + 1 by omega, List.getElem?_cons_succ]

def optOK : Option (List (Nat × Bool)) → Option (List (Nat × Bool)) → Bool
  | none, _ => true
  | some c, some d => clEq c d
  | some _, none => false

def allNone : List (Option (List (Nat × Bool))) → Bool
  | [] => true
  | none :: xs => allNone xs
  | some _ :: _ => false

/-- `T` holds clause `c` at key `k` whenever the `k`-th element of `xs` is `some c`. -/
def agreeT : CT → List (Option (List (Nat × Bool))) → Bool
  | _, [] => true
  | .nil, xs => allNone xs
  | .node v l r, x :: xs => optOK x v && agreeT l (splitP xs).1 && agreeT r (splitP xs).2

theorem allNone_get : ∀ (xs : List (Option (List (Nat × Bool)))) (k : Nat) (c : List (Nat × Bool)),
    allNone xs = true → xs[k]? = some (some c) → False
  | [], k, c, _, h => by simp at h
  | none :: xs, 0, c, _, h => by simp at h
  | none :: xs, k + 1, c, ha, h => allNone_get xs k c ha (by simpa using h)
  | some _ :: _, _, _, ha, _ => by simp [allNone] at ha

theorem agreeT_sound : ∀ (t : CT) (xs : List (Option (List (Nat × Bool)))),
    agreeT t xs = true → ∀ k c, xs[k]? = some (some c) → t.get k = some c
  | _, [], _, k, c, h => by simp at h
  | .nil, x :: xs, ha, k, c, h => absurd (allNone_get (x :: xs) k c ha h) id
  | .node v l r, x :: xs, ha, k, c, h => by
    simp only [agreeT, Bool.and_eq_true] at ha
    obtain ⟨⟨h0, hl⟩, hr⟩ := ha
    cases k with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at h
      subst h
      cases v with
      | none => simp [optOK] at h0
      | some d => simp only [optOK] at h0; rw [clEq_eq _ _ h0]; rfl
    | succ k =>
      simp only [List.getElem?_cons_succ] at h
      show NT.get (.node v l r) (k + 1) = some c
      simp only [NT.get]
      cases hk : Nat.beq (k % 2) 0
      · have hk' : k % 2 = 1 := by have := Nat.ne_of_beq_eq_false hk; omega
        simp only [cond]
        apply agreeT_sound r _ hr (k / 2) c
        rw [(splitP_get xs (k / 2)).2, show 2 * (k / 2) + 1 = k by omega]; exact h
      · have hk' : k % 2 = 0 := Nat.eq_of_beq_eq_true hk
        simp only [cond]
        apply agreeT_sound l _ hl (k / 2) c
        rw [(splitP_get xs (k / 2)).1, show 2 * (k / 2) = k by omega]; exact h

theorem unsat_of_agreeT (F : List (List (Nat × Bool))) (T : CT) (N : Nat)
    (hag : agreeT T (none :: F.map some) = true) (hch : ChainOK T (F.length + 1) (N + 1)) (hN1 : 1 ≤ N)
    (hN : T.get N = some []) :
    ∀ a : Nat → Bool, F.all (fun c => c.any (fun l => a l.1 == l.2)) = false := by
  intro a
  cases hF : F.all (fun c => c.any (fun l => a l.1 == l.2))
  · rfl
  · exfalso
    have h0 : SatBelow a T (F.length + 1) := by
      intro k c h1 h2 hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : j < F.length := by omega
      have hget := agreeT_sound T _ hag (j + 1) (F[j]) (by
        rw [List.getElem?_cons_succ, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl)
      rw [hk] at hget
      cases hget
      exact (List.all_eq_true.mp hF) _ (List.getElem_mem hj)
    have := hch a h0 N [] hN1 (by omega) hN
    simp [ClauseTrue] at this

/-- `NT.get` with recursors and `Nat` primitives. -/
noncomputable def NT.getK {α : Type} (t : NT α) : Nat → Option α :=
  NT.rec (motive := fun _ => Nat → Option α) (fun _ => none)
    (fun v _ _ ihl ihr k => Nat.casesOn (motive := fun _ => Option α) k v
      (fun k' => Bool.casesOn (motive := fun _ => Option α) (Nat.beq (Nat.mod k' 2) 0)
        (ihr (Nat.div k' 2)) (ihl (Nat.div k' 2)))) t

theorem NT.getK_eq {α : Type} : ∀ (t : NT α) (k : Nat), t.getK k = t.get k
  | .nil, k => by cases k <;> rfl
  | .node v l r, 0 => rfl
  | .node v l r, k + 1 => by
    show Bool.casesOn (motive := fun _ => Option α) (Nat.beq (Nat.mod k 2) 0) (r.getK (Nat.div k 2))
      (l.getK (Nat.div k 2)) = NT.get (.node v l r) (k + 1)
    rw [NT.getK_eq l, NT.getK_eq r]
    show _ = cond (Nat.beq (k % 2) 0) (l.get (k / 2)) (r.get (k / 2))
    cases Nat.beq (Nat.mod k 2) 0 <;> rfl

/-- `LratBits.step` with the `Nat` primitives spelled out. -/
def stepK (cp cn pa na u : Nat) : Step :=
  cond (Nat.beq (Nat.lor (Nat.land cp pa) (Nat.land cn na)) 0)
    (let a := Nat.lor pa na
     let up := Nat.xor cp (Nat.land cp a)
     let un := Nat.xor cn (Nat.land cn a)
     cond (Nat.beq up 0)
       (cond (Nat.beq un 0) .conflict
         (cond (Nat.beq un (Nat.shiftLeft 1 u)) (.unit pa (Nat.lor na un)) .skip))
       (cond (Nat.beq un 0)
         (cond (Nat.beq up (Nat.shiftLeft 1 u)) (.unit (Nat.lor pa up) na) .skip)
         .skip))
    .skip

theorem stepK_eq : stepK = step := rfl

noncomputable def propR (T : CT) (id : Nat) (hs : List (Nat × Nat)) : Nat → Nat → Bool :=
  List.rec (motive := fun _ => Nat → Nat → Bool) (fun _ _ => false)
    (fun hu _ ih pa na => Prod.casesOn (motive := fun _ => Bool) hu fun h u =>
      cond (Nat.ble 1 h && Nat.ble (Nat.succ h) id)
        (Option.casesOn (motive := fun _ => Bool) (T.getK h) false fun c =>
          Prod.casesOn (motive := fun _ => Bool) (litsBits c 0 0) fun cp cn =>
            Step.casesOn (motive := fun _ => Bool) (stepK cp cn pa na u) true
              (fun pa' na' => ih pa' na') (ih pa na))
        false) hs

theorem propR_eq (T : CT) (id : Nat) : ∀ (hs : List (Nat × Nat)) (pa na : Nat),
    propR T id hs pa na = propT T id pa na hs
  | [], _, _ => rfl
  | (h, u) :: hs, pa, na => by
    unfold propR
    dsimp only
    rw [NT.getK_eq, stepK_eq]
    simp only [propT]
    have hb : Nat.ble (Nat.succ h) id = Nat.blt h id := rfl
    rw [hb]
    cases Nat.ble 1 h && Nat.blt h id
    · rfl
    · simp only [cond]
      cases T.get h with
      | none => rfl
      | some c =>
        dsimp only
        cases litsBits c 0 0 with
        | mk cp cn =>
          dsimp only
          cases step cp cn pa na u with
          | conflict => rfl
          | unit pa' na' => exact propR_eq T id hs pa' na'
          | skip => exact propR_eq T id hs pa na

noncomputable def stepOkR (T : CT) (id : Nat) (hints : List (Nat × Nat)) : Bool :=
  Option.casesOn (motive := fun _ => Bool) (T.getK id) false fun c =>
    Prod.casesOn (motive := fun _ => Bool) (litsBits c 0 0) fun cp cn =>
      cond (Nat.beq (Nat.land cp cn) 0) (propR T id hints cn cp) true

theorem stepOkR_eq (T : CT) (id : Nat) (hints : List (Nat × Nat)) : stepOkR T id hints = stepOk T id hints := by
  unfold stepOkR stepOk
  rw [NT.getK_eq]
  cases T.get id with
  | none => rfl
  | some c =>
    dsimp only
    cases litsBits c 0 0 with
    | mk cp cn =>
      dsimp only
      rw [propR_eq]; rfl

/-- `chkChunk` with recursors (the form the driver gives to the kernel). -/
noncomputable def chkR (T : CT) (id : Nat) (steps : List (List (Nat × Nat))) : Bool :=
  List.rec (motive := fun _ => Nat → Bool) (fun _ => true)
    (fun hs _ ih id => stepOkR T id hs && ih (Nat.succ id)) steps id

theorem chkR_eq (T : CT) : ∀ (steps : List (List (Nat × Nat))) (id : Nat), chkR T id steps = chkChunk T id steps
  | [], _ => rfl
  | hs :: rest, id => by
    show (stepOkR T id hs && chkR T (Nat.succ id) rest) = chkChunk T id (hs :: rest)
    rw [stepOkR_eq, chkR_eq T rest]; rfl

theorem chkR_sound (T : CT) (steps : List (List (Nat × Nat))) (id : Nat) (h : chkR T id steps = true) :
    ChainOK T id (id + steps.length) :=
  chkChunk_sound T steps id (by rw [← chkR_eq]; exact h)

end BVS
