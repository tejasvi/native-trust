import BVS.Lrat.Chain
import BVS.Sound.CNF
/-!
# A clause tree whose leaves are gate descriptors

The original clauses are not stored as literal lists: a leaf `Leaf.gt k l r j` stands for the
`j`-th Tseitin clause of the gate `k = l ∧ r` (`Leaf.clause`). The base check then compares the
bit-blaster's entries with the leaves (four numbers per leaf) instead of building and comparing
clause lists; the chunk checker sees `Leaf.clause` of the looked-up leaf.
-/
namespace BVS
open LratBits

inductive Leaf where
  | gt (k l r j : Nat)
  | cl (c : Clause)

def Leaf.clause : Leaf → Clause
  | .gt k l _ 0 => [(k, false), litC l]
  | .gt k _ r 1 => [(k, false), litC r]
  | .gt k l r _ => [(k, true), litC (neg l), litC (neg r)]
  | .cl c => c

def gateLeaves : List Ent → List Leaf → List Leaf
  | [], acc => acc
  | .gate k l r :: es, acc => gateLeaves es (.gt k l r 0 :: .gt k l r 1 :: .gt k l r 2 :: acc)
  | .atom .. :: es, acc => gateLeaves es acc

/-- The leaves of the CNF `cnfOf es out`, in order. -/
def leavesOf (es : List Ent) (out : Nat) : List Leaf :=
  .cl [litC out] :: .cl [(0, false)] :: gateLeaves es []

theorem gateLeaves_clause : ∀ (es : List Ent) (acc : List Leaf),
    (gateLeaves es acc).map Leaf.clause = gateClauses es (acc.map Leaf.clause)
  | [], acc => rfl
  | .gate k l r :: es, acc => by
    simp only [gateLeaves, gateClauses]
    rw [gateLeaves_clause es]
    rfl
  | .atom .. :: es, acc => by
    simp only [gateLeaves, gateClauses]
    exact gateLeaves_clause es acc

theorem leavesOf_clause (es : List Ent) (out : Nat) : (leavesOf es out).map Leaf.clause = cnfOf es out := by
  simp only [leavesOf, cnfOf, List.map_cons]
  rw [gateLeaves_clause]
  rfl

def leafEq : Leaf → Leaf → Bool
  | .gt k l r j, .gt k' l' r' j' => Nat.beq k k' && Nat.beq l l' && Nat.beq r r' && Nat.beq j j'
  | .cl c, .cl c' => clEq c c'
  | _, _ => false

theorem leafEq_eq : ∀ (a b : Leaf), leafEq a b = true → a = b
  | .gt k l r j, .gt k' l' r' j', h => by
    simp only [leafEq, Bool.and_eq_true] at h
    obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3, Nat.eq_of_beq_eq_true h4]
  | .cl c, .cl c', h => by simp only [leafEq] at h; rw [clEq_eq _ _ h]
  | .gt .., .cl _, h => by simp [leafEq] at h
  | .cl _, .gt .., h => by simp [leafEq] at h

/-- The clause tree: a perfect binary tree of leaves, in key order. -/
inductive LTree where
  | leaf (v : Option Leaf)
  | node (l r : LTree)

def LTree.get : LTree → Nat → Nat → Option Leaf
  | .leaf v, _, _ => v
  | .node l r, half, k => cond (Nat.ble half k) (LTree.get r (half / 2) (k - half)) (LTree.get l (half / 2) k)

def leafOK : Option Leaf → Option Leaf → Bool
  | none, _ => true
  | some a, some b => leafEq a b
  | some _, none => false

def agreeL : LTree → Nat → List (Option Leaf) → Option (List (Option Leaf))
  | _, _, [] => some []
  | .leaf v, 0, x :: xs => cond (leafOK x v) (some xs) none
  | .leaf _, _ + 1, _ :: _ => none
  | .node _ _, 0, _ :: _ => none
  | .node l r, d + 1, xs =>
    match agreeL l d xs with
    | some ys => agreeL r d ys
    | none => none

theorem leafOK_get {x v : Option Leaf} {c : Leaf} (h : leafOK x v = true) (hx : x = some c) : v = some c := by
  subst hx
  cases v with
  | none => simp [leafOK] at h
  | some d => simp only [leafOK] at h; rw [leafEq_eq _ _ h]

theorem agreeL_sound : ∀ (t : LTree) (d : Nat) (xs ys : List (Option Leaf)), agreeL t d xs = some ys →
    (∀ k c, k < 2 ^ d → xs[k]? = some (some c) → t.get (2 ^ d / 2) k = some c) ∧ ys = xs.drop (2 ^ d)
  | t, d, [], ys, h => by
    cases t <;> cases d <;> (simp only [agreeL, Option.some.injEq] at h; subst h; exact ⟨fun k c _ hk => by simp at hk, by simp⟩)
  | .leaf v, 0, x :: xs, ys, h => by
    simp only [agreeL] at h
    cases ho : leafOK x v
    · rw [ho] at h; simp [cond] at h
    · rw [ho] at h; simp only [cond, Option.some.injEq] at h; subst h
      refine ⟨fun k c hk hx => ?_, by simp⟩
      have : k = 0 := by simpa using hk
      subst this
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      exact leafOK_get ho hx
  | .leaf v, d + 1, x :: xs, ys, h => by simp [agreeL] at h
  | .node l r, 0, x :: xs, ys, h => by simp [agreeL] at h
  | .node l r, d + 1, x :: xs', ys, h => by
    simp only [agreeL] at h
    generalize hxs : x :: xs' = xs at h ⊢
    cases h1 : agreeL l d xs with
    | none => rw [h1] at h; simp at h
    | some ys1 =>
      rw [h1] at h; simp only at h
      obtain ⟨hl, e1⟩ := agreeL_sound l d xs ys1 h1
      obtain ⟨hr, e2⟩ := agreeL_sound r d ys1 ys h
      have hp : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; omega
      refine ⟨fun k c hk hx => ?_, by rw [e2, e1, List.drop_drop, Nat.pow_succ]; congr 1; omega⟩
      simp only [LTree.get, hp, nat_ble_eq, cond_decide]
      by_cases hkd : 2 ^ d ≤ k
      · rw [if_pos hkd]
        apply hr (k - 2 ^ d) c (by rw [Nat.pow_succ] at hk; omega)
        rw [e1, List.getElem?_drop, show 2 ^ d + (k - 2 ^ d) = k by omega]; exact hx
      · rw [if_neg hkd]; exact hl k c (by omega) hx

noncomputable def LTree.getR (t : LTree) : Nat → Nat → Option Leaf :=
  LTree.rec (motive := fun _ => Nat → Nat → Option Leaf) (fun v _ _ => v)
    (fun _ _ ihl ihr half k => Bool.casesOn (motive := fun _ => Option Leaf) (Nat.ble half k)
      (ihl (Nat.div half 2) k) (ihr (Nat.div half 2) (Nat.sub k half))) t

theorem LTree.getR_eq : ∀ (t : LTree) (half k : Nat), t.getR half k = t.get half k
  | .leaf v, _, _ => rfl
  | .node l r, half, k => by
    show Bool.casesOn (motive := fun _ => Option Leaf) (Nat.ble half k)
      (l.getR (Nat.div half 2) k) (r.getR (Nat.div half 2) (Nat.sub k half)) = LTree.get (.node l r) half k
    rw [LTree.getR_eq l, LTree.getR_eq r]
    show _ = cond (Nat.ble half k) (r.get (half / 2) (k - half)) (l.get (half / 2) k)
    cases Nat.ble half k <;> rfl

/-- The lookup the chunk checker uses: the clause of the leaf. -/
noncomputable def look4 (T : LTree) (H : Nat) : Nat → Option Clause := fun k =>
  Option.casesOn (motive := fun _ => Option Clause) (T.getR H k) none (fun leaf => some leaf.clause)

theorem look4_eq (T : LTree) (H k : Nat) : look4 T H k = (T.get H k).map Leaf.clause := by
  unfold look4; rw [LTree.getR_eq]; cases T.get H k <;> rfl

end BVS
