import BVS.LratBits
/-!
# Soundness of `LratBits.checkBits`

`unsat_list_of_checkBits`: if `checkBits F acts = true`, then no assignment satisfies every
clause of `F` (a clause `c : List (Nat × Bool)` is satisfied by `a` when some literal `(v, b) ∈ c`
has `a v = b`). The proof uses core lemmas only (`Nat.testBit_*`).
-/
namespace LratBits

/-- A clause given as a literal list is true under `a`. -/
def ClauseTrue (a : Nat → Bool) (c : List (Nat × Bool)) : Prop :=
  c.any (fun l => a l.1 == l.2) = true

/-- A bitmask clause is true under `a`. -/
def BSat (a : Nat → Bool) (c : Nat × Nat) : Prop :=
  ∃ v, (c.1.testBit v = true ∧ a v = true) ∨ (c.2.testBit v = true ∧ a v = false)

/-- Every clause in the store is true under `a`. -/
def Models (a : Nat → Bool) (t : CTrie) : Prop := ∀ k c, t.get k = some c → BSat a c

/-- `a` extends the partial assignment `(pa, na)`. -/
def Cons (a : Nat → Bool) (pa na : Nat) : Prop :=
  ∀ v, (pa.testBit v = true → a v = true) ∧ (na.testBit v = true → a v = false)

theorem cT {α : Type} (x y : α) : cond true x y = x := rfl
theorem cF {α : Type} (x y : α) : cond false x y = y := rfl

/-! ## The clause store -/

namespace CTrie

theorem force_eq (t : CTrie) (k : CTrie → CTrie) : force t k = k t := by
  cases t <;> rfl

theorem get_nil (k : Nat) : get .nil k = none := by
  cases k <;> rfl

theorem get_node_zero (v : Option (Nat × Nat)) (l r : CTrie) : get (.node v l r) 0 = v := rfl

theorem get_node_succ (v : Option (Nat × Nat)) (l r : CTrie) (k : Nat) :
    get (.node v l r) (k + 1) = cond (Nat.beq (k % 2) 0) (get l (k / 2)) (get r (k / 2)) := rfl

theorem ins_zero (t : CTrie) (k : Nat) (c : Nat × Nat) : ins 0 t k c = t := rfl

theorem ins_nil_zero (n : Nat) (c : Nat × Nat) : ins (n + 1) .nil 0 c = .node (some c) .nil .nil := rfl

theorem ins_nil_succ (n k : Nat) (c : Nat × Nat) :
    ins (n + 1) .nil (k + 1) c = cond (Nat.beq (k % 2) 0)
      (.node none (ins n .nil (k / 2) c) .nil) (.node none .nil (ins n .nil (k / 2) c)) := by
  show cond _ (force _ _) (force _ _) = _
  rw [force_eq, force_eq]

theorem ins_node_zero (n : Nat) (v : Option (Nat × Nat)) (l r : CTrie) (c : Nat × Nat) :
    ins (n + 1) (.node v l r) 0 c = .node (some c) l r := rfl

theorem ins_node_succ (n : Nat) (v : Option (Nat × Nat)) (l r : CTrie) (k : Nat) (c : Nat × Nat) :
    ins (n + 1) (.node v l r) (k + 1) c = cond (Nat.beq (k % 2) 0)
      (.node v (ins n l (k / 2) c) r) (.node v l (ins n r (k / 2) c)) := by
  show cond _ (force _ _) (force _ _) = _
  rw [force_eq, force_eq]

/-- Every clause of the store after an insertion was there before, or is the inserted one. -/
theorem get_ins : ∀ (n : Nat) (t : CTrie) (k : Nat) (c : Nat × Nat) (j : Nat) (d : Nat × Nat),
    get (ins n t k c) j = some d → get t j = some d ∨ d = c := by
  intro n
  induction n with
  | zero => intro t k c j d h; exact Or.inl h
  | succ n ih =>
    intro t k c j d h
    cases t with
    | nil =>
      right
      cases k with
      | zero =>
        rw [ins_nil_zero] at h
        cases j with
        | zero => rw [get_node_zero] at h; exact (Option.some.inj h).symm
        | succ j =>
          rw [get_node_succ, get_nil] at h
          cases Nat.beq (j % 2) 0 <;> exact absurd h (by simp)
      | succ k =>
        rw [ins_nil_succ] at h
        cases hk : Nat.beq (k % 2) 0 <;> rw [hk] at h
        · cases j with
          | zero => rw [cF, get_node_zero] at h; exact absurd h (by simp)
          | succ j =>
            rw [cF, get_node_succ, get_nil] at h
            cases hj : Nat.beq (j % 2) 0 <;> rw [hj] at h
            · rw [cF] at h
              rcases ih .nil (k / 2) c (j / 2) d h with h' | h'
              · rw [get_nil] at h'; exact absurd h' (by simp)
              · exact h'
            · rw [cT] at h; exact absurd h (by simp)
        · cases j with
          | zero => rw [cT, get_node_zero] at h; exact absurd h (by simp)
          | succ j =>
            rw [cT, get_node_succ, get_nil] at h
            cases hj : Nat.beq (j % 2) 0 <;> rw [hj] at h
            · rw [cF] at h; exact absurd h (by simp)
            · rw [cT] at h
              rcases ih .nil (k / 2) c (j / 2) d h with h' | h'
              · rw [get_nil] at h'; exact absurd h' (by simp)
              · exact h'
    | node v l r =>
      cases k with
      | zero =>
        rw [ins_node_zero] at h
        cases j with
        | zero => rw [get_node_zero] at h; exact Or.inr (Option.some.inj h).symm
        | succ j => rw [get_node_succ] at h; exact Or.inl (by rw [get_node_succ]; exact h)
      | succ k =>
        rw [ins_node_succ] at h
        cases hk : Nat.beq (k % 2) 0 <;> rw [hk] at h
        · rw [cF] at h
          cases j with
          | zero => rw [get_node_zero] at h; exact Or.inl (by rw [get_node_zero]; exact h)
          | succ j =>
            rw [get_node_succ] at h
            rw [get_node_succ]
            cases hj : Nat.beq (j % 2) 0 <;> rw [hj] at h
            · rw [cF] at h; rw [cF]; exact ih r (k / 2) c (j / 2) d h
            · rw [cT] at h; rw [cT]; exact Or.inl h
        · rw [cT] at h
          cases j with
          | zero => rw [get_node_zero] at h; exact Or.inl (by rw [get_node_zero]; exact h)
          | succ j =>
            rw [get_node_succ] at h
            rw [get_node_succ]
            cases hj : Nat.beq (j % 2) 0 <;> rw [hj] at h
            · rw [cF] at h; rw [cF]; exact Or.inl h
            · rw [cT] at h; rw [cT]; exact ih l (k / 2) c (j / 2) d h

end CTrie

theorem models_ins {a : Nat → Bool} {t : CTrie} (hm : Models a t) (k : Nat) {c : Nat × Nat}
    (hc : BSat a c) : Models a (CTrie.ins 64 t k c) := by
  intro j d h
  rcases CTrie.get_ins 64 t k c j d h with h' | h'
  · exact hm j d h'
  · rw [h']; exact hc

/-! ## Bit facts -/

theorem testBit_one_shiftLeft (k v : Nat) : (1 <<< k).testBit v = decide (k = v) := by
  rw [Nat.one_shiftLeft, Nat.testBit_two_pow]

theorem eq_of_beq {x y : Nat} (h : Nat.beq x y = true) : x = y := Nat.eq_of_beq_eq_true h

theorem testBit_eq_false_of_zero {x : Nat} (h : x = 0) (v : Nat) : x.testBit v = false := by
  rw [h, Nat.zero_testBit]

/-- Bits of `c ^^^ (c &&& a)`: the bits of `c` outside `a`. -/
theorem testBit_diff (c a v : Nat) :
    (c ^^^ (c &&& a)).testBit v = (c.testBit v && !a.testBit v) := by
  rw [Nat.testBit_xor, Nat.testBit_and]
  cases c.testBit v <;> cases a.testBit v <;> rfl

/-! ## One hint -/

/-- `step` is sound: a conflict contradicts every model extending the assignment, and a unit
extends it. -/
theorem step_spec {a : Nat → Bool} {cp cn pa na u : Nat} (hs : BSat a (cp, cn)) (hc : Cons a pa na) :
    match step cp cn pa na u with
    | .conflict => False
    | .unit pa' na' => Cons a pa' na'
    | .skip => True := by
  unfold step
  cases hS : Nat.beq ((cp &&& pa) ||| (cn &&& na)) 0
  · rw [cF]; trivial
  · rw [cT]
    dsimp only
    have hS0 := eq_of_beq hS
    -- no literal of the clause is true under (pa, na)
    have hp : ∀ v, cp.testBit v = true → pa.testBit v = false := by
      intro v hv
      have := testBit_eq_false_of_zero hS0 v
      rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, hv, Bool.true_and] at this
      cases h1 : pa.testBit v
      · rfl
      · rw [h1, Bool.true_or] at this; exact absurd this (by simp)
    have hn : ∀ v, cn.testBit v = true → na.testBit v = false := by
      intro v hv
      have := testBit_eq_false_of_zero hS0 v
      rw [Nat.testBit_or, Nat.testBit_and, Nat.testBit_and, hv, Bool.true_and] at this
      cases h1 : na.testBit v
      · rfl
      · rw [h1, Bool.or_true] at this; exact absurd this (by simp)
    obtain ⟨w, hw⟩ := hs
    -- abbreviations
    generalize hup : cp ^^^ (cp &&& (pa ||| na)) = up
    generalize hun : cn ^^^ (cn &&& (pa ||| na)) = un
    have hupb : ∀ v, up.testBit v = (cp.testBit v && !(pa.testBit v || na.testBit v)) := by
      intro v; rw [← hup, testBit_diff, Nat.testBit_or]
    have hunb : ∀ v, un.testBit v = (cn.testBit v && !(pa.testBit v || na.testBit v)) := by
      intro v; rw [← hun, testBit_diff, Nat.testBit_or]
    -- a positive literal of the clause that is not unassigned is false: its variable is false
    have posF : ∀ v, cp.testBit v = true → up.testBit v = false → a v = false := by
      intro v hv hu
      rw [hupb, hv, hp v hv, Bool.false_or, Bool.true_and] at hu
      cases h1 : na.testBit v
      · rw [h1] at hu; exact absurd hu (by simp)
      · exact (hc v).2 h1
    have negF : ∀ v, cn.testBit v = true → un.testBit v = false → a v = true := by
      intro v hv hu
      rw [hunb, hv, hn v hv, Bool.or_false, Bool.true_and] at hu
      cases h1 : pa.testBit v
      · rw [h1] at hu; exact absurd hu (by simp)
      · exact (hc v).1 h1
    cases hu0 : Nat.beq up 0
    · rw [cF]
      cases hn0 : Nat.beq un 0
      · rw [cF]; trivial
      · rw [cT]
        have hun0 := eq_of_beq hn0
        cases hb : Nat.beq up (1 <<< u)
        · rw [cF]; trivial
        · rw [cT]
          have hb' := eq_of_beq hb
          -- the unit literal is the positive literal `log2 up`; it must be true
          have key : a (u) = true := by
            rcases hw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
            · cases hk : decide (u = w)
              · have : up.testBit w = false := by rw [hb', testBit_one_shiftLeft, hk]
                rw [posF w hw1 this] at hw2; exact absurd hw2 (by simp)
              · rw [of_decide_eq_true hk]; exact hw2
            · rw [negF w hw1 (testBit_eq_false_of_zero hun0 w)] at hw2; exact absurd hw2 (by simp)
          intro v
          refine ⟨fun h => ?_, fun h => (hc v).2 h⟩
          rw [Nat.testBit_or] at h
          cases h1 : pa.testBit v
          · rw [h1, Bool.false_or, hb', testBit_one_shiftLeft] at h
            rw [← of_decide_eq_true h]; exact key
          · exact (hc v).1 h1
    · rw [cT]
      have hup0 := eq_of_beq hu0
      cases hn0 : Nat.beq un 0
      · rw [cF]
        cases hb : Nat.beq un (1 <<< u)
        · rw [cF]; trivial
        · rw [cT]
          have hb' := eq_of_beq hb
          have key : a (u) = false := by
            rcases hw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
            · rw [posF w hw1 (testBit_eq_false_of_zero hup0 w)] at hw2; exact absurd hw2 (by simp)
            · cases hk : decide (u = w)
              · have : un.testBit w = false := by rw [hb', testBit_one_shiftLeft, hk]
                rw [negF w hw1 this] at hw2; exact absurd hw2 (by simp)
              · rw [of_decide_eq_true hk]; exact hw2
          intro v
          refine ⟨fun h => (hc v).1 h, fun h => ?_⟩
          rw [Nat.testBit_or] at h
          cases h1 : na.testBit v
          · rw [h1, Bool.false_or, hb', testBit_one_shiftLeft] at h
            rw [← of_decide_eq_true h]; exact key
          · exact (hc v).2 h1
      · rw [cT]
        have hun0 := eq_of_beq hn0
        rcases hw with ⟨hw1, hw2⟩ | ⟨hw1, hw2⟩
        · rw [posF w hw1 (testBit_eq_false_of_zero hup0 w)] at hw2; exact absurd hw2 (by simp)
        · rw [negF w hw1 (testBit_eq_false_of_zero hun0 w)] at hw2; exact absurd hw2 (by simp)

/-! ## Propagation and RUP -/

theorem prop_sound {a : Nat → Bool} {t : CTrie} (hm : Models a t) :
    ∀ (hints : List (Nat × Nat)) (pa na : Nat), prop t pa na hints = true → Cons a pa na → False := by
  intro hints
  induction hints with
  | nil => intro pa na h _; exact absurd h (by simp [prop])
  | cons hu hs ih =>
    obtain ⟨h, u⟩ := hu
    intro pa na hp hc
    unfold prop at hp
    cases hg : t.get h with
    | none => rw [hg] at hp; exact absurd hp (by simp)
    | some cc =>
      obtain ⟨cp, cn⟩ := cc
      rw [hg] at hp
      dsimp only at hp
      have hspec := step_spec (u := u) (hm h (cp, cn) hg) hc
      revert hp hspec
      cases step cp cn pa na u with
      | conflict => intro _ hspec; exact hspec
      | unit pa' na' => intro hp hspec; exact ih pa' na' hp hspec
      | skip => intro hp _; exact ih pa na hp hc

theorem rupOk_sound {a : Nat → Bool} {t : CTrie} (hm : Models a t) (cp cn : Nat) (hints : List (Nat × Nat))
    (h : rupOk t cp cn hints = true) : BSat a (cp, cn) := by
  unfold rupOk at h
  cases hb : Nat.beq (cp &&& cn) 0
  · -- a tautology: some variable occurs in both polarities
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
  · rw [hb, cT] at h
    apply Classical.byContradiction
    intro hns
    apply prop_sound hm hints cn cp h
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

/-! ## The certificate -/

theorem runChunk_sound {a : Nat → Bool} : ∀ (acts : List BAct) (t : CTrie), Models a t →
    match runChunk t acts with
    | .done b => b = true → False
    | .cont t' => Models a t' := by
  intro acts
  induction acts with
  | nil => intro t hm; exact hm
  | cons x xs ih =>
    intro t hm
    cases x with
    | unsupported => intro h; exact absurd h (by simp)
    | rup id cp cn hints =>
      unfold runChunk
      cases hr : rupOk t cp cn hints
      · rw [cF]; intro h; exact absurd h (by simp)
      · rw [cT]
        have hsat := rupOk_sound hm cp cn hints hr
        cases hz : Nat.beq (cp ||| cn) 0
        · rw [cF]
          have hm' := models_ins hm id hsat
          revert hm'
          cases CTrie.ins 64 t id (cp, cn) with
          | nil => intro hm'; exact ih .nil hm'
          | node v l r => intro hm'; exact ih (.node v l r) hm'
        · rw [cT]
          intro _
          have hz0 := eq_of_beq hz
          obtain ⟨w, hw⟩ := hsat
          have h1 : cp.testBit w = false := by
            have := testBit_eq_false_of_zero hz0 w
            rw [Nat.testBit_or] at this
            cases h : cp.testBit w
            · rfl
            · rw [h, Bool.true_or] at this; exact this
          have h2 : cn.testBit w = false := by
            have := testBit_eq_false_of_zero hz0 w
            rw [Nat.testBit_or] at this
            cases h : cn.testBit w
            · rfl
            · rw [h, Bool.or_true] at this; exact this
          rcases hw with ⟨hw1, _⟩ | ⟨hw1, _⟩
          · rw [h1] at hw1; exact absurd hw1 (by simp)
          · rw [h2] at hw1; exact absurd hw1 (by simp)

theorem runAll_sound {a : Nat → Bool} : ∀ (cs : List (List BAct)) (t : CTrie), Models a t →
    runAll t cs = true → False := by
  intro cs
  induction cs with
  | nil => intro t _ h; exact absurd h (by simp [runAll])
  | cons c cs ih =>
    intro t hm h
    unfold runAll at h
    have hc := runChunk_sound c t hm
    revert h hc
    cases runChunk t c with
    | done b => intro h hb; exact hb h
    | cont t' => intro h hm'; exact ih t' hm' h

/-! ## The initial clause store -/

theorem litsBits_sat {a : Nat → Bool} : ∀ (c : List (Nat × Bool)) (cp cn : Nat),
    ClauseTrue a c ∨ BSat a (cp, cn) → BSat a (litsBits c cp cn) := by
  intro c
  induction c with
  | nil =>
    intro cp cn h
    rcases h with h | h
    · exact absurd h (by simp [ClauseTrue])
    · exact h
  | cons l ls ih =>
    intro cp cn h
    obtain ⟨v, b⟩ := l
    unfold litsBits
    cases b with
    | true =>
      rw [cT]
      apply ih
      rcases h with h | h
      · unfold ClauseTrue at h
        rw [List.any_cons, Bool.or_eq_true] at h
        rcases h with h | h
        · right
          refine ⟨v, Or.inl ⟨?_, ?_⟩⟩
          · show (cp ||| 1 <<< v).testBit v = true
            rw [Nat.testBit_or, testBit_one_shiftLeft]; simp
          · simpa using h
        · left; exact h
      · right
        obtain ⟨w, hw⟩ := h
        refine ⟨w, ?_⟩
        rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; refine ⟨?_, h2⟩
          show (cp ||| 1 <<< v).testBit w = true
          rw [Nat.testBit_or, h1, Bool.true_or]
        · right; exact ⟨h1, h2⟩
    | false =>
      rw [cF]
      apply ih
      rcases h with h | h
      · unfold ClauseTrue at h
        rw [List.any_cons, Bool.or_eq_true] at h
        rcases h with h | h
        · right
          refine ⟨v, Or.inr ⟨?_, ?_⟩⟩
          · show (cn ||| 1 <<< v).testBit v = true
            rw [Nat.testBit_or, testBit_one_shiftLeft]; simp
          · simpa using h
        · left; exact h
      · right
        obtain ⟨w, hw⟩ := h
        refine ⟨w, ?_⟩
        rcases hw with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · left; exact ⟨h1, h2⟩
        · right; refine ⟨?_, h2⟩
          show (cn ||| 1 <<< v).testBit w = true
          rw [Nat.testBit_or, h1, Bool.true_or]

theorem initTrie_sound {a : Nat → Bool} : ∀ (F : List (List (Nat × Bool))),
    (∀ c, c ∈ F → ClauseTrue a c) → ∀ (i : Nat) (t : CTrie), Models a t → Models a (initTrie F i t) := by
  intro F
  induction F with
  | nil => intro _ i t hm; exact hm
  | cons c cs ih =>
    intro hF i t hm
    unfold initTrie
    rw [CTrie.force_eq]
    apply ih (fun c' hc' => hF c' (List.mem_cons_of_mem c hc'))
    apply models_ins hm
    apply litsBits_sat
    left; exact hF c (List.mem_cons_self ..)

/-- **Soundness.** If the checker accepts, no assignment satisfies all clauses of `F`. -/
theorem unsat_list_of_checkBits (F : List (List (Nat × Bool))) (acts : List (List BAct))
    (h : checkBits F acts = true) (a : Nat → Bool) :
    F.all (fun c => c.any (fun l => a l.1 == l.2)) = false := by
  cases hF : F.all (fun c => c.any (fun l => a l.1 == l.2))
  · rfl
  · exfalso
    have hc : ∀ c, c ∈ F → ClauseTrue a c := fun c hc => (List.all_eq_true.mp hF) c hc
    have hm := initTrie_sound F hc 1 .nil (fun k c h => by rw [CTrie.get_nil] at h; exact absurd h (by simp))
    exact runAll_sound acts _ hm h

end LratBits
