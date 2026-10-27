module

public import BVS.Blast

@[expose] public section
/-!
# Soundness of the bit-blaster: literals, the state invariant, gates
-/
namespace BVS
open Std.Tactic.BVDecide

/-! ## Boolean lemmas for kernel-style definitions -/

theorem nat_beq_eq (a b : Nat) : Nat.beq a b = decide (a = b) := by
  cases h : Nat.beq a b
  · have := Nat.ne_of_beq_eq_false h; simp [this]
  · have := Nat.eq_of_beq_eq_true h; simp [this]

theorem nat_ble_eq (a b : Nat) : Nat.ble a b = decide (a ≤ b) := by
  cases h : Nat.ble a b
  · have : ¬ a ≤ b := fun h' => by rw [Nat.ble_eq_true_of_le h'] at h; contradiction
    simp [this]
  · have := Nat.le_of_ble_eq_true h; simp [this]

theorem nat_blt_eq (a b : Nat) : Nat.blt a b = decide (a < b) := by
  show Nat.ble (a + 1) b = _
  rw [nat_ble_eq]; rfl

theorem cond_decide {α : Type} (p : Prop) [Decidable p] (x y : α) :
    cond (decide p) x y = if p then x else y := by
  by_cases h : p <;> simp [h]

/-! ## Literals -/

/-- The value of literal `l` under a valuation `env` of the nodes. -/
def lv (env : Nat → Bool) (l : Nat) : Bool := cond (Nat.beq (l % 2) 0) (env (l / 2)) (!env (l / 2))

theorem lv_eq (env : Nat → Bool) (l : Nat) :
    lv env l = if l % 2 = 0 then env (l / 2) else !env (l / 2) := by
  simp only [lv, nat_beq_eq, cond_decide]

theorem lv_zero {env : Nat → Bool} (h : env 0 = false) : lv env 0 = false := by
  simp [lv_eq, h]

theorem lv_one {env : Nat → Bool} (h : env 0 = false) : lv env 1 = true := by
  simp [lv_eq, h]

theorem lv_two_mul (env : Nat → Bool) (k : Nat) : lv env (2 * k) = env k := by
  rw [lv_eq]; simp

theorem lv_neg (env : Nat → Bool) (l : Nat) : lv env (neg l) = !lv env l := by
  simp only [neg, nat_beq_eq, cond_decide, lv_eq]
  by_cases h : l % 2 = 0
  · have h1 : (l + 1) % 2 ≠ 0 := by omega
    have h2 : (l + 1) / 2 = l / 2 := by omega
    simp [h, h1, h2]
  · have h1 : (l - 1) % 2 = 0 := by omega
    have h2 : (l - 1) / 2 = l / 2 := by omega
    simp [h, h1, h2]

/-- The carry of a full adder. -/
def majB (a b c : Bool) : Bool := ((a ^^ b) && c) || (a && b)

/-! ## Bool-list semantics of the arithmetic circuits -/

/-- Ripple-carry addition on bit lists (least significant first). -/
def addL : List Bool → List Bool → Bool → List Bool × Bool
  | a :: as, b :: bs, c => (((a ^^ b) ^^ c) :: (addL as bs (majB a b c)).1, (addL as bs (majB a b c)).2)
  | _, _, c => ([], c)

def allL : List Bool → Bool
  | [] => true
  | b :: bs => b && allL bs

/-- The first `n` elements, padded with `false`. -/
def takeDL : Nat → List Bool → List Bool
  | 0, _ => []
  | n + 1, [] => false :: takeDL n []
  | n + 1, b :: bs => b :: takeDL n bs

def shlL (as : List Bool) (i : Nat) : List Bool := takeDL as.length (List.replicate i false ++ as)

def mulL (as : List Bool) : List Bool → Nat → List Bool → List Bool
  | [], _, acc => acc
  | b :: bs, i, acc => mulL as bs (i + 1) (if b then (addL acc (shlL as i) false).1 else acc)

def shiftConcatL (l : List Bool) (b : Bool) : List Bool := takeDL l.length (b :: l)

def divStepL (n d : List Bool) (wn : Nat) (q r : List Bool) : List Bool × List Bool :=
  let r' := shiftConcatL r (n.getD (wn - 1) false)
  let ad := addL r' (d.map not) true
  (if ad.2 then shiftConcatL q true else shiftConcatL q false, if ad.2 then ad.1 else r')

def divGoL (n d : List Bool) : Nat → Nat → List Bool → List Bool → List Bool × List Bool
  | 0, _, q, r => (q, r)
  | k + 1, wn, q, r => divGoL n d k (wn - 1) (divStepL n d wn q r).1 (divStepL n d wn q r).2

/-- The value of word operation `c` (`opCode`) on bit lists. -/
def binSemC (c : Nat) (as bs : List Bool) : List Bool :=
  match c with
  | 0 => List.zipWith (· && ·) as bs
  | 1 => List.zipWith (· || ·) as bs
  | 2 => List.zipWith (· ^^ ·) as bs
  | 3 => (addL as bs false).1
  | 4 => mulL as bs 0 (List.replicate as.length false)
  | 5 => if allL (List.zipWith (· == ·) bs (List.replicate as.length false)) then List.replicate as.length false
      else (divGoL as bs as.length as.length (List.replicate as.length false) (List.replicate as.length false)).1
  | _ => if allL (List.zipWith (· == ·) bs (List.replicate as.length false)) then as
      else (divGoL as bs as.length as.length (List.replicate as.length false) (List.replicate as.length false)).2

/-! ## Entries, valuations, the invariant -/

/-- The equation of a defining entry under `env`; `av v i` is bit `i` of variable `v`. -/
def Ent.holds (av : Nat → Nat → Bool) (env : Nat → Bool) : Ent → Prop
  | .gate k l r => env k = (lv env l && lv env r)
  | .atom k v i => env k = av v i

/-- `env` respects every defining entry of `st`, and node `0` is false. -/
def Good (av : Nat → Nat → Bool) (env : Nat → Bool) (st : St) : Prop :=
  env 0 = false ∧ ∀ e ∈ st.es, e.holds av env

/-- The memo tables are correct under every valuation that respects the entries. -/
def MemoOK (st : St) : Prop :=
  ∀ av env, Good av env st →
    (∀ c xs ys zs, (c, xs, ys, zs) ∈ st.mb → ys.length = xs.length →
      zs.map (lv env) = binSemC c (xs.map (lv env)) (ys.map (lv env))) ∧
    (∀ xs ys z q r, (xs, ys, z, q, r) ∈ st.md → ys.length = xs.length →
      lv env z = allL (List.zipWith (· == ·) (ys.map (lv env)) (List.replicate xs.length false)) ∧
      q.map (lv env) = (divGoL (xs.map (lv env)) (ys.map (lv env)) xs.length xs.length
        (List.replicate xs.length false) (List.replicate xs.length false)).1 ∧
      r.map (lv env) = (divGoL (xs.map (lv env)) (ys.map (lv env)) xs.length xs.length
        (List.replicate xs.length false) (List.replicate xs.length false)).2)

/-- Every input-cache entry names atom entries, and the memo tables are correct. -/
def Inv (st : St) : Prop :=
  (∀ v ks, st.ha.get v = some ks → ∀ i (h : i < ks.length), Ent.atom ks[i] v i ∈ st.es) ∧ MemoOK st

theorem MemoOK.mono {st st' : St} (h : MemoOK st) (hb : st'.mb = st.mb) (hd : st'.md = st.md)
    (he : ∀ e ∈ st.es, e ∈ st'.es) : MemoOK st' := by
  intro av env g
  have g' : Good av env st := ⟨g.1, fun e h' => g.2 e (he e h')⟩
  obtain ⟨h1, h2⟩ := h av env g'
  exact ⟨fun c xs ys zs hm => h1 c xs ys zs (hb ▸ hm), fun xs ys z q r hm => h2 xs ys z q r (hd ▸ hm)⟩

/-- `st'` extends `st`: it keeps all entries and the invariant. -/
def Ext (st st' : St) : Prop := (∀ e ∈ st.es, e ∈ st'.es) ∧ (Inv st → Inv st')

theorem Ext.refl (st : St) : Ext st st := ⟨fun _ h => h, id⟩

theorem Ext.trans {a b c : St} (h1 : Ext a b) (h2 : Ext b c) : Ext a c :=
  ⟨fun e h => h2.1 e (h1.1 e h), fun h => h2.2 (h1.2 h)⟩

theorem Good.mono {av env} {st st' : St} (h : Ext st st') (g : Good av env st') : Good av env st :=
  ⟨g.1, fun e he => g.2 e (h.1 e he)⟩

theorem Good.lv0 {av env} {st : St} (g : Good av env st) : lv env 0 = false := lv_zero g.1
theorem Good.lv1 {av env} {st : St} (g : Good av env st) : lv env 1 = true := lv_one g.1

theorem inv_empty : Inv St.empty := by
  refine ⟨fun v ks h => ?_, fun av env _ => ⟨fun c xs ys zs h => ?_, fun xs ys z q r h => ?_⟩⟩
  · simp [St.empty, NT.get] at h
  · simp [St.empty] at h
  · simp [St.empty] at h

/-- The specification shape of every construction step. -/
def Spec {α : Type} (av : Nat → Nat → Bool) (st : St) (p : St × α) (P : (Nat → Bool) → α → Prop) : Prop :=
  Ext st p.1 ∧ (Inv st → ∀ env, Good av env p.1 → P env p.2)

/-! ## The trie -/

namespace NT

theorem get_nil {α : Type} (k : Nat) : get (nil : NT α) k = none := by cases k <;> rfl

theorem get_node_zero {α : Type} (v : Option α) (l r : NT α) : get (node v l r) 0 = v := rfl

theorem get_node_succ {α : Type} (v : Option α) (l r : NT α) (j : Nat) :
    get (node v l r) (j + 1) = if j % 2 = 0 then get l (j / 2) else get r (j / 2) := by
  simp only [get, nat_beq_eq, cond_decide]

theorem upd_nil_zero {α : Type} (n : Nat) (f : Option α → α) :
    upd (n + 1) nil 0 f = node (some (f none)) nil nil := rfl

theorem upd_nil_succ {α : Type} (n k : Nat) (f : Option α → α) :
    upd (n + 1) nil (k + 1) f = if k % 2 = 0 then node none (upd n nil (k / 2) f) nil
      else node none nil (upd n nil (k / 2) f) := by
  simp only [upd, nat_beq_eq, cond_decide]

theorem upd_node_zero {α : Type} (n : Nat) (v : Option α) (l r : NT α) (f : Option α → α) :
    upd (n + 1) (node v l r) 0 f = node (some (f v)) l r := rfl

theorem upd_node_succ {α : Type} (n : Nat) (v : Option α) (l r : NT α) (k : Nat) (f : Option α → α) :
    upd (n + 1) (node v l r) (k + 1) f = if k % 2 = 0 then node v (upd n l (k / 2) f) r
      else node v l (upd n r (k / 2) f) := by
  simp only [upd, nat_beq_eq, cond_decide]

theorem get_upd {α : Type} : ∀ (n : Nat) (t : NT α) (k : Nat) (f : Option α → α) (j : Nat) (x : α),
    get (upd n t k f) j = some x → (j = k ∧ x = f (get t k)) ∨ get t j = some x := by
  intro n
  induction n with
  | zero => intro t k f j x h; exact Or.inr h
  | succ n ih =>
    intro t k f j x h
    cases t with
    | nil =>
      cases k with
      | zero =>
        rw [upd_nil_zero] at h
        cases j with
        | zero => rw [get_node_zero] at h; left; exact ⟨rfl, by rw [get_nil]; exact (Option.some.inj h).symm⟩
        | succ j => rw [get_node_succ] at h; split at h <;> simp [get_nil] at h
      | succ k =>
        rw [upd_nil_succ] at h
        cases j with
        | zero => split at h <;> simp [get_node_zero] at h
        | succ j =>
          split at h <;> rw [get_node_succ] at h <;> split at h <;> (try simp [get_nil] at h)
          · rcases ih nil (k / 2) f (j / 2) x h with ⟨e1, e2⟩ | e3
            · left; refine ⟨by omega, by rw [e2, get_nil, get_nil]⟩
            · simp [get_nil] at e3
          · rcases ih nil (k / 2) f (j / 2) x h with ⟨e1, e2⟩ | e3
            · left; refine ⟨by omega, by rw [e2, get_nil, get_nil]⟩
            · simp [get_nil] at e3
    | node v l r =>
      cases k with
      | zero =>
        rw [upd_node_zero] at h
        cases j with
        | zero => rw [get_node_zero] at h; left; exact ⟨rfl, by rw [get_node_zero]; exact (Option.some.inj h).symm⟩
        | succ j => right; rw [get_node_succ] at h ⊢; exact h
      | succ k =>
        rw [upd_node_succ] at h
        cases j with
        | zero => right; split at h <;> (rw [get_node_zero] at h ⊢; exact h)
        | succ j =>
          split at h <;> rename_i hk <;> rw [get_node_succ] at h <;> split at h <;> rename_i hj
          · rcases ih l (k / 2) f (j / 2) x h with ⟨e1, e2⟩ | e3
            · left; refine ⟨by omega, by rw [e2, get_node_succ, if_pos hk]⟩
            · right; rw [get_node_succ, if_pos hj]; exact e3
          · right; rw [get_node_succ, if_neg hj]; exact h
          · right; rw [get_node_succ, if_pos hj]; exact h
          · rcases ih r (k / 2) f (j / 2) x h with ⟨e1, e2⟩ | e3
            · left; refine ⟨by omega, by rw [e2, get_node_succ, if_neg hk]⟩
            · right; rw [get_node_succ, if_neg hj]; exact e3

end NT

theorem assoc_cons {r a k : Nat} {rest : List (Nat × Nat)} {x : Nat}
    (h : assoc r ((a, k) :: rest) = some x) : (a = r ∧ x = k) ∨ assoc r rest = some x := by
  simp only [assoc, nat_beq_eq, cond_decide] at h
  split at h
  · left; exact ⟨by assumption, (Option.some.inj h).symm⟩
  · right; exact h

/-! ## AND gates -/

theorem mkAnd_spec (av : Nat → Nat → Bool) (st : St) (a b : Nat) :
    Spec av st (mkAnd st a b) (fun env o => lv env o = (lv env a && lv env b)) := by
  -- the ordered inputs
  have hlr : ∀ env, (lv env (cond (Nat.ble a b) a b) && lv env (cond (Nat.ble a b) b a)) =
      (lv env a && lv env b) := by
    intro env; cases Nat.ble a b <;> simp [Bool.and_comm]
  have hle : cond (Nat.ble a b) a b ≤ cond (Nat.ble a b) b a := by
    rw [nat_ble_eq]; by_cases h : a ≤ b <;> simp [h] <;> omega
  unfold mkAnd
  generalize cond (Nat.ble a b) a b = l at hlr hle ⊢
  generalize cond (Nat.ble a b) b a = r at hlr hle ⊢
  simp only [nat_beq_eq, ← Bool.decide_and, cond_decide]
  by_cases h0 : l = 0
  · simp only [h0, if_true]
    refine ⟨Ext.refl st, fun _ env g => ?_⟩
    dsimp only; rw [← hlr env, h0, g.lv0]; simp
  simp only [h0, if_false]
  by_cases h1 : l = 1
  · simp only [h1, if_true]
    refine ⟨Ext.refl st, fun _ env g => ?_⟩
    dsimp only; rw [← hlr env, h1, g.lv1]; simp
  simp only [h1, if_false]
  by_cases h2 : l = r
  · simp only [h2, if_true]
    refine ⟨Ext.refl st, fun _ env g => ?_⟩
    dsimp only; rw [← hlr env, h2]; simp
  simp only [h2, if_false]
  by_cases h3 : l % 2 = 0 ∧ l + 1 = r
  · simp only [h3, and_self, if_true]
    refine ⟨Ext.refl st, fun _ env g => ?_⟩
    dsimp only; rw [← hlr env, g.lv0]
    have : r = neg l := by simp [neg, h3.1]; omega
    rw [this, lv_neg]; simp
  simp only [h3, if_false]
  refine ⟨⟨fun e he => List.mem_cons_of_mem _ he, fun hinv => ⟨?_, ?_⟩⟩, fun _ env g => ?_⟩
  · intro v ks h i hi
    exact List.mem_cons_of_mem _ (hinv.1 v ks h i hi)
  · exact hinv.2.mono rfl rfl (fun e he => List.mem_cons_of_mem _ he)
  · have := g.2 _ (List.mem_cons_self ..)
    simp only [Ent.holds] at this
    dsimp only
    rw [lv_two_mul, this, hlr env]

end BVS
