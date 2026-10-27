import BVS.Unsat
/-!
# The base check split across declarations

`check4` evaluates in one declaration the bit-blaster on the whole problem, the well-formedness check
`wfEs` and the agreement of the clause tree with the CNF's leaves. The kernel keeps the intermediate
terms of a declaration, so its memory grows with the problem (in our runs, a single base check of a
588k-clause problem exceeded a 48 GB address-space limit), and about three quarters of its work are
the well-formedness and agreement passes. Here the parts are split:

* `blastCk bv es n out` (one declaration): the bit-blaster's run on `bv` gives the entry list `es`
  (given as data, a concatenation `seg_m ++ (… ++ (seg_1 ++ []))` of segments), the next node `n` and
  the output literal `out`;
* `segOK` (one declaration per segment): well-formedness of the segment against the bound left by the
  newer segments (`wfEs_append`), and agreement of its leaves with the clause tree at their key range,
  by an in-order pass over that range (`agreeFrom`); `acc_step` adds a segment to the checked part;
* `bvs_unsat5` assembles these with the chunk chain and the empty clause.
-/
namespace BVS
open Std.Tactic.BVDecide LratBits

/-! ## The bit-blaster's run, compared with data -/

def entEq : Ent → Ent → Bool
  | .gate k l r, .gate k' l' r' => Nat.beq k k' && Nat.beq l l' && Nat.beq r r'
  | .atom k v i, .atom k' v' i' => Nat.beq k k' && Nat.beq v v' && Nat.beq i i'
  | _, _ => false

theorem entEq_eq : ∀ (a b : Ent), entEq a b = true → a = b
  | .gate k l r, .gate k' l' r', h => by
    simp only [entEq, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3]
  | .atom k v i, .atom k' v' i', h => by
    simp only [entEq, Bool.and_eq_true] at h
    obtain ⟨⟨h1, h2⟩, h3⟩ := h
    rw [Nat.eq_of_beq_eq_true h1, Nat.eq_of_beq_eq_true h2, Nat.eq_of_beq_eq_true h3]
  | .gate .., .atom .., h => by simp [entEq] at h
  | .atom .., .gate .., h => by simp [entEq] at h

def esEq : List Ent → List Ent → Bool
  | [], [] => true
  | a :: as, b :: bs => entEq a b && esEq as bs
  | _, _ => false

theorem esEq_eq : ∀ (xs ys : List Ent), esEq xs ys = true → xs = ys
  | [], [], _ => rfl
  | a :: as, b :: bs, h => by
    simp only [esEq, Bool.and_eq_true] at h
    rw [entEq_eq a b h.1, esEq_eq as bs h.2]
  | [], _ :: _, h => by simp [esEq] at h
  | _ :: _, [], h => by simp [esEq] at h

/-- `bv` uses supported constructors, and the bit-blaster's run on it gives the entries `es`, the next
node `n` and the output literal `out`. -/
def blastCk (bv : BVLogicalExpr) (es : List Ent) (n out : Nat) : Bool :=
  supportedBool bv &&
  (match blastBool St.empty bv with
   | (st, o) => Nat.beq st.n n && Nat.beq o out && esEq st.es es)

theorem blastCk_sound {bv : BVLogicalExpr} {es : List Ent} {n out : Nat} (h : blastCk bv es n out = true) :
    supportedBool bv = true ∧ (blastBool St.empty bv).1.es = es ∧ (blastBool St.empty bv).1.n = n ∧
      (blastBool St.empty bv).2 = out := by
  unfold blastCk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨hs, h⟩ := h
  generalize blastBool St.empty bv = p at h ⊢
  rcases p with ⟨st, o⟩
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hn, ho⟩, he⟩ := h
  exact ⟨hs, esEq_eq _ _ he, Nat.eq_of_beq_eq_true hn, Nat.eq_of_beq_eq_true ho⟩

/-! ## Well-formedness of a concatenation of segments -/

/-- The node of the last (oldest) entry of a segment, or `b` for the empty segment: the bound for the
segments below it. -/
def lastK : List Ent → Nat → Nat
  | [], b => b
  | .gate k _ _ :: es, _ => lastK es k
  | .atom k _ _ :: es, _ => lastK es k

theorem wfEs_append : ∀ (xs ys : List Ent) (b : Nat), wfEs xs b = true → wfEs ys (lastK xs b) = true →
    wfEs (List.append xs ys) b = true
  | [], _, _, _, h => h
  | .gate k l r :: xs, ys, b, h1, h2 => by
    simp only [wfEs, Bool.and_eq_true] at h1
    show wfEs (.gate k l r :: List.append xs ys) b = true
    simp only [wfEs, Bool.and_eq_true]
    exact ⟨h1.1, wfEs_append xs ys k h1.2 h2⟩
  | .atom k v i :: xs, ys, b, h1, h2 => by
    simp only [wfEs, Bool.and_eq_true] at h1
    show wfEs (.atom k v i :: List.append xs ys) b = true
    simp only [wfEs, Bool.and_eq_true]
    exact ⟨h1.1, wfEs_append xs ys k h1.2 h2⟩

/-! ## The leaves of a concatenation -/

theorem gateLeaves_acc : ∀ (es : List Ent) (acc : List Leaf), gateLeaves es acc = gateLeaves es [] ++ acc
  | [], _ => rfl
  | .gate k l r :: es, acc => by
    simp only [gateLeaves]
    rw [gateLeaves_acc es (_ :: _ :: _ :: acc), gateLeaves_acc es [_, _, _]]
    simp
  | .atom .. :: es, acc => by
    simp only [gateLeaves]
    exact gateLeaves_acc es acc

theorem gateLeaves_append_acc : ∀ (xs ys : List Ent) (acc : List Leaf),
    gateLeaves (List.append xs ys) acc = gateLeaves ys (gateLeaves xs acc)
  | [], _, _ => rfl
  | .gate k l r :: xs, ys, acc => by
    show gateLeaves (.gate k l r :: List.append xs ys) acc = _
    simp only [gateLeaves]
    exact gateLeaves_append_acc xs ys _
  | .atom k v i :: xs, ys, acc => by
    show gateLeaves (.atom k v i :: List.append xs ys) acc = _
    simp only [gateLeaves]
    exact gateLeaves_append_acc xs ys acc

theorem gateLeaves_append (xs ys : List Ent) :
    gateLeaves (List.append xs ys) [] = gateLeaves ys [] ++ gateLeaves xs [] := by
  rw [gateLeaves_append_acc, gateLeaves_acc]

/-! ## Agreement of a list of leaves with the clause tree at a key range -/

/-- The leaves `xs` are at keys `lo, lo + 1, …` of `T` (lookup with `H = 2^D / 2`). -/
def AgreeAt (T : LTree) (H lo : Nat) (xs : List Leaf) : Prop :=
  ∀ i c, xs[i]? = some c → T.get H (lo + i) = some c

theorem AgreeAt.nil (T : LTree) (H lo : Nat) : AgreeAt T H lo [] := fun i c h => by simp at h

theorem AgreeAt.append {T : LTree} {H lo : Nat} {xs ys : List Leaf} (h1 : AgreeAt T H lo xs)
    (h2 : AgreeAt T H (lo + xs.length) ys) : AgreeAt T H lo (xs ++ ys) := by
  intro i c h
  by_cases hi : i < xs.length
  · rw [List.getElem?_append_left hi] at h
    exact h1 i c h
  · have hi' : xs.length ≤ i := Nat.le_of_not_lt hi
    rw [List.getElem?_append_right hi'] at h
    have := h2 (i - xs.length) c h
    rwa [show lo + xs.length + (i - xs.length) = lo + i by omega] at this

/-- In-order pass over the keys `lo, lo + 1, …` of a subtree of depth `d` (keys `0 … 2^d - 1`),
comparing the leaves with `xs`; returns the leaves not placed in this subtree. -/
def agreeFrom : LTree → Nat → Nat → List Leaf → Option (List Leaf)
  | _, _, _, [] => some []
  | .leaf v, 0, lo, x :: xs => cond (Nat.beq lo 0 && leafOK (some x) v) (some xs) none
  | .leaf _, _ + 1, _, _ :: _ => none
  | .node _ _, 0, _, _ :: _ => none
  | .node l r, d + 1, lo, x :: xs =>
    cond (Nat.ble (2 ^ d) lo) (agreeFrom r d (lo - 2 ^ d) (x :: xs))
      (match agreeFrom l d lo (x :: xs) with
       | some ys => agreeFrom r d 0 ys
       | none => none)

theorem agreeFrom_sound : ∀ (t : LTree) (d lo : Nat) (xs ys : List Leaf), agreeFrom t d lo xs = some ys →
    (∀ i c, lo + i < 2 ^ d → xs[i]? = some c → t.get (2 ^ d / 2) (lo + i) = some c) ∧
      ys = xs.drop (2 ^ d - lo)
  | t, d, lo, [], ys, h => by
    have : ys = [] := by
      cases t <;> cases d <;> (simp only [agreeFrom, Option.some.injEq] at h; exact h.symm)
    subst this
    exact ⟨fun i c _ hc => by simp at hc, by simp⟩
  | .leaf v, 0, lo, x :: xs, ys, h => by
    simp only [agreeFrom] at h
    cases hc : (Nat.beq lo 0 && leafOK (some x) v)
    · rw [hc] at h; simp [cond] at h
    · rw [hc] at h
      simp only [cond, Option.some.injEq] at h
      subst h
      simp only [Bool.and_eq_true] at hc
      have hlo : lo = 0 := Nat.eq_of_beq_eq_true hc.1
      subst hlo
      refine ⟨fun i c hi hx => ?_, by simp⟩
      have : i = 0 := by simpa using hi
      subst this
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hx
      subst hx
      exact leafOK_get hc.2 rfl
  | .leaf _, _ + 1, _, _ :: _, _, h => by simp [agreeFrom] at h
  | .node _ _, 0, _, _ :: _, _, h => by simp [agreeFrom] at h
  | .node l r, d + 1, lo, x :: xs, ys, h => by
    simp only [agreeFrom] at h
    have hp : 2 ^ (d + 1) / 2 = 2 ^ d := by rw [Nat.pow_succ]; omega
    have hpow : 2 ^ (d + 1) = 2 ^ d + 2 ^ d := by rw [Nat.pow_succ]; omega
    cases hlo : Nat.ble (2 ^ d) lo
    · rw [hlo] at h
      simp only [cond] at h
      have hlo' : lo < 2 ^ d := by
        rw [nat_ble_eq] at hlo
        simp at hlo
        omega
      cases h1 : agreeFrom l d lo (x :: xs) with
      | none => rw [h1] at h; simp at h
      | some ys1 =>
        rw [h1] at h
        simp only at h
        obtain ⟨hl, e1⟩ := agreeFrom_sound l d lo _ ys1 h1
        obtain ⟨hr, e2⟩ := agreeFrom_sound r d 0 ys1 ys h
        refine ⟨fun i c hi hx => ?_, ?_⟩
        · simp only [LTree.get, hp, nat_ble_eq, cond_decide]
          by_cases hk : 2 ^ d ≤ lo + i
          · rw [if_pos hk]
            have := hr (lo + i - 2 ^ d) c (by omega)
              (by rw [e1, List.getElem?_drop, show 2 ^ d - lo + (lo + i - 2 ^ d) = i by omega]; exact hx)
            rwa [Nat.zero_add] at this
          · rw [if_neg hk]
            exact hl i c (by omega) hx
        · rw [e2, e1, List.drop_drop]
          congr 1
          omega
    · rw [hlo] at h
      simp only [cond] at h
      have hlo' : 2 ^ d ≤ lo := Nat.le_of_ble_eq_true hlo
      obtain ⟨hr, e2⟩ := agreeFrom_sound r d (lo - 2 ^ d) _ ys h
      refine ⟨fun i c hi hx => ?_, ?_⟩
      · simp only [LTree.get, hp, nat_ble_eq, cond_decide]
        rw [if_pos (by omega)]
        have := hr i c (by omega) hx
        rwa [show lo - 2 ^ d + i = lo + i - 2 ^ d by omega] at this
      · rw [e2]
        congr 1
        omega

/-- All of `xs` placed at keys `lo, lo + 1, …` of the tree `T` of depth `D`. -/
def agreeSeg (T : LTree) (D lo : Nat) (xs : List Leaf) : Bool :=
  match agreeFrom T D lo xs with
  | some [] => true
  | _ => false

theorem agreeSeg_sound {T : LTree} {D lo : Nat} {xs : List Leaf} (h : agreeSeg T D lo xs = true) :
    AgreeAt T (2 ^ D / 2) lo xs := by
  unfold agreeSeg at h
  cases ha : agreeFrom T D lo xs with
  | none => rw [ha] at h; simp at h
  | some ys =>
    rw [ha] at h
    have hys : ys = [] := by cases ys <;> simp_all
    subst hys
    obtain ⟨hget, hdrop⟩ := agreeFrom_sound T D lo xs [] ha
    intro i c hc
    have hi : i < xs.length := by
      rcases Nat.lt_or_ge i xs.length with h' | h'
      · exact h'
      · rw [List.getElem?_eq_none h'] at hc; simp at hc
    have hfit : xs.length ≤ 2 ^ D - lo := by
      have := congrArg List.length hdrop
      simp at this
      omega
    exact hget i c (by omega) hc

/-! ## Segments -/

/-- One segment `seg` (newest entry first) below the bound `b`, whose oldest entry leaves the bound
`bprev` for the older segments; its `len` leaves are at keys `lo, lo + 1, …` of `T`. -/
def segOK (T : LTree) (D lo : Nat) (seg : List Ent) (b bprev len : Nat) : Bool :=
  agreeSeg T D lo (gateLeaves seg []) && wfEs seg b && Nat.beq (lastK seg b) bprev &&
    Nat.beq (gateLeaves seg []).length len

/-- The clause tree's dimensions: `H = 2^D / 2` (lookups with `H` on the tree of depth `D`). -/
def dimsOK (D H : Nat) : Bool := Nat.beq H (2 ^ D / 2)

/-- The checked part of the entries: leaves at keys `3, 4, …`, their number, well-formedness. -/
def EntsOK (T : LTree) (H : Nat) (es : List Ent) (len b : Nat) : Prop :=
  AgreeAt T H 3 (gateLeaves es []) ∧ (gateLeaves es []).length = len ∧ wfEs es b = true

theorem entsOK_nil (T : LTree) (H b : Nat) : EntsOK T H [] 0 b :=
  ⟨AgreeAt.nil T H 3, rfl, rfl⟩

theorem acc_step {T : LTree} {D H : Nat} (hH : dimsOK D H = true) {seg rest : List Ent} {b bprev lenR len lo : Nat}
    (hlo : Nat.beq lo (3 + lenR) = true) (hprev : EntsOK T H rest lenR bprev)
    (hseg : segOK T D lo seg b bprev len = true) :
    EntsOK T H (List.append seg rest) (lenR + len) b := by
  have hH' : H = 2 ^ D / 2 := Nat.eq_of_beq_eq_true hH
  have hlo' : lo = 3 + lenR := Nat.eq_of_beq_eq_true hlo
  unfold segOK at hseg
  simp only [Bool.and_eq_true] at hseg
  obtain ⟨⟨⟨hag, hwf⟩, hlast⟩, hlen⟩ := hseg
  have hlen' := Nat.eq_of_beq_eq_true hlen
  have hlast' := Nat.eq_of_beq_eq_true hlast
  obtain ⟨pag, plen, pwf⟩ := hprev
  refine ⟨?_, ?_, ?_⟩
  · rw [gateLeaves_append]
    apply AgreeAt.append pag
    rw [plen, show 3 + lenR = lo by omega, hH']
    exact agreeSeg_sound hag
  · rw [gateLeaves_append, List.length_append, plen, hlen']
  · exact wfEs_append seg rest b hwf (by rw [hlast']; exact pwf)

/-! ## The end-to-end statement with the split base check -/

theorem bvs_unsat5 (bv : BVLogicalExpr) (T : LTree) (D H L N n out lenG : Nat) (es : List Ent)
    (hb : blastCk bv es n out = true)
    (hH : dimsOK D H = true)
    (hacc : EntsOK T H es lenG n)
    (h12 : agreeSeg T D 1 [.cl [litC out], .cl [(0, false)]] = true)
    (hL : Nat.beq L (lenG + 2) = true)
    (hch : ChainL (look4 T H) (L + 1) (N + 1)) (he : stepEmpty4 T D H N = true) : bv.Unsat := by
  have hH' : H = 2 ^ D / 2 := Nat.eq_of_beq_eq_true hH
  have hL' := Nat.eq_of_beq_eq_true hL
  obtain ⟨pag, plen, pwf⟩ := hacc
  obtain ⟨hs, hes, hn, hout⟩ := blastCk_sound hb
  have hwf : wfEs (blastBool St.empty bv).1.es (blastBool St.empty bv).1.n = true := by rw [hes, hn]; exact pwf
  apply unsat_of_cnf bv hs hwf
  rw [hes, hout]
  have h2 := agreeSeg_sound h12
  rw [← hH'] at h2
  have hag : AgreeAt T H 1 (leavesOf es out) := by
    have := AgreeAt.append h2 (show AgreeAt T H (1 + 2) (gateLeaves es []) from pag)
    exact this
  have hlen : (leavesOf es out).length = L := by
    simp only [leavesOf, List.length_cons, plen]
    omega
  rw [← leavesOf_clause]
  intro a
  cases hFa : ((leavesOf es out).map Leaf.clause).all (fun c => c.any (fun l => a l.1 == l.2))
  · rfl
  · exfalso
    simp only [stepEmpty4, Bool.and_eq_true] at he
    obtain ⟨⟨hN1, hN2⟩, hN⟩ := he
    have hN' : look4 T H N = some [] := by
      rw [look4_eq]
      revert hN; cases T.get H N with
      | none => simp
      | some c => cases c with
        | gt k l r j => simp
        | cl c => cases c <;> simp [Leaf.clause]
    have h0 : SatBelowL a (look4 T H) (L + 1) := by
      intro k c h1 h2 hk
      obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
      have hj : j < (leavesOf es out).length := by omega
      have := hag j (leavesOf es out)[j] (List.getElem?_eq_getElem hj)
      rw [show 1 + j = j + 1 by omega] at this
      rw [look4_eq, this] at hk
      simp only [Option.map_some, Option.some.injEq] at hk
      subst hk
      exact (List.all_eq_true.mp hFa) _ (List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩)
    have := hch a h0 N [] (Nat.le_of_ble_eq_true hN1) (by omega) hN'
    simp [LratBits.ClauseTrue] at this

end BVS
