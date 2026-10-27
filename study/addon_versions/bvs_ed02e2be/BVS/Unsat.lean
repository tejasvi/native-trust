import BVS.Lrat.LeafTree
/-!
# The end-to-end statement with a single base check

`bvs_unsat4`: a `bv_decide` problem `bv` is unsatisfiable if
* `check4 bv T D H L` (kernel evaluation): `bv` uses supported constructors, the bit-blaster's
  entries are well formed, the CNF has `L` clauses, and the leaf tree `T` (depth `D`,
  `H = 2^D / 2`) holds the CNF's leaves (`leavesOf`, gate descriptors) at ids `1 … L`;
* `ChainL (look4 T H) (L + 1) (N + 1)`: the learned clauses follow by unit propagation;
* `stepEmpty4 T D H N`: the leaf at id `N` is the empty clause.
-/
namespace BVS
open Std.Tactic.BVDecide

def check4 (bv : BVLogicalExpr) (T : LTree) (D H L : Nat) : Bool :=
  supportedBool bv && Nat.beq H (2 ^ D / 2) &&
  (match blastBool St.empty bv with
   | (st, out) => wfEs st.es st.n &&
      (Nat.beq (leavesOf st.es out).length L &&
        (match agreeL T D (none :: (leavesOf st.es out).map some) with
         | some [] => true
         | _ => false)))

def stepEmpty4 (T : LTree) (D H N : Nat) : Bool :=
  Nat.ble 1 N && Nat.blt N (2 ^ D) && (match T.get H N with | some (.cl []) => true | _ => false)

theorem bvs_unsat4 (bv : BVLogicalExpr) (T : LTree) (D H L N : Nat) (h : check4 bv T D H L = true)
    (hch : ChainL (look4 T H) (L + 1) (N + 1)) (he : stepEmpty4 T D H N = true) : bv.Unsat := by
  unfold check4 at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨hs, hH⟩, h⟩ := h
  have hH' := Nat.eq_of_beq_eq_true hH
  generalize hb : blastBool St.empty bv = p at h
  rcases p with ⟨st, out⟩
  simp only [Bool.and_eq_true] at h
  obtain ⟨hwf, hl, hag⟩ := h
  have hl' := Nat.eq_of_beq_eq_true hl
  generalize hLv : leavesOf st.es out = Lv at hl' hag
  have hF : cnfOf st.es out = Lv.map Leaf.clause := by rw [← hLv, leavesOf_clause]
  cases ha : agreeL T D (none :: Lv.map some) with
  | none => rw [ha] at hag; simp at hag
  | some ys =>
    rw [ha] at hag
    have hys : ys = [] := by cases ys <;> simp_all
    obtain ⟨hget, hdrop⟩ := agreeL_sound T D _ ys ha
    have hfit : Lv.length + 1 ≤ 2 ^ D := by
      have : (List.drop (2 ^ D) (none :: Lv.map some)).length = 0 := by rw [← hdrop, hys]; rfl
      simp at this; omega
    simp only [stepEmpty4, Bool.and_eq_true] at he
    obtain ⟨⟨hN1, hN2⟩, hN⟩ := he
    have hN' : look4 T H N = some [] := by
      rw [look4_eq]
      revert hN; cases T.get H N with
      | none => simp
      | some c => cases c with
        | gt k l r j => simp
        | cl c => cases c <;> simp [Leaf.clause]
    apply unsat_of_cnf bv hs (by rw [hb]; exact hwf)
    rw [hb]
    simp only
    rw [hF]
    intro a
    cases hFa : (Lv.map Leaf.clause).all (fun c => c.any (fun l => a l.1 == l.2))
    · rfl
    · exfalso
      have h0 : SatBelowL a (look4 T H) (L + 1) := by
        intro k c h1 h2 hk
        obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
        have hj : j < Lv.length := by omega
        have := hget (j + 1) (Lv[j]) (by omega) (by
          rw [List.getElem?_cons_succ, List.getElem?_map, List.getElem?_eq_getElem hj]; rfl)
        rw [← hH'] at this
        rw [look4_eq, this] at hk
        simp only [Option.map_some, Option.some.injEq] at hk
        subst hk
        exact (List.all_eq_true.mp hFa) _ (List.mem_map.mpr ⟨_, List.getElem_mem hj, rfl⟩)
      have := hch a h0 N [] (Nat.le_of_ble_eq_true hN1) (by omega) hN'
      simp [LratBits.ClauseTrue] at this

end BVS
