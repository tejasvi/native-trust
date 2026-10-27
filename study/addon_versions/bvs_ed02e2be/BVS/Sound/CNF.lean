import BVS.Sound.Expr
/-!
# Soundness of the bit-blaster: the valuation of well-formed entries, the CNF

`unsat_of_cnf`: if the expression is supported, the entries pass `wfEs`, and the CNF `cnfOf` is
unsatisfiable, then the `bv_decide` problem `bv` is unsatisfiable (`BVLogicalExpr.Unsat`).
-/
namespace BVS
open Std.Tactic.BVDecide

def Ent.node : Ent → Nat
  | .gate k _ _ => k
  | .atom k _ _ => k

def Ent.value (av : Nat → Nat → Bool) (env : Nat → Bool) : Ent → Bool
  | .gate _ l r => lv env l && lv env r
  | .atom _ v i => av v i

/-- The valuation defined by entries listed newest first. -/
def envOf (av : Nat → Nat → Bool) : List Ent → Nat → Bool
  | [], _ => false
  | e :: es, j => if j = e.node then e.value av (envOf av es) else envOf av es j

theorem lv_congr {env env' : Nat → Bool} {l : Nat} (h : env (l / 2) = env' (l / 2)) :
    lv env l = lv env' l := by
  simp [lv, h]

/-- The facts `wfEs` checks, for every entry. -/
def EntOK (b : Nat) : Ent → Prop
  | .gate k l r => 1 ≤ k ∧ k < b ∧ l / 2 < k ∧ r / 2 < k
  | .atom k _ _ => 1 ≤ k ∧ k < b

theorem EntOK.node_lt {b : Nat} {e : Ent} (h : EntOK b e) : 1 ≤ e.node ∧ e.node < b := by
  cases e <;> simp only [EntOK, Ent.node] at h ⊢ <;> omega

theorem EntOK.mono {b b' : Nat} {e : Ent} (h : EntOK b e) (hb : b ≤ b') : EntOK b' e := by
  cases e <;> simp only [EntOK] at h ⊢ <;> omega

theorem wfEs_cons {e : Ent} {es : List Ent} {b : Nat} (h : wfEs (e :: es) b = true) :
    EntOK b e ∧ wfEs es e.node = true := by
  cases e with
  | gate k l r =>
    simp only [wfEs, Bool.and_eq_true, nat_blt_eq, nat_ble_eq, decide_eq_true_eq] at h
    exact ⟨⟨h.1.1.1.2, h.1.1.1.1, h.1.1.2, h.1.2⟩, h.2⟩
  | atom k v i =>
    simp only [wfEs, Bool.and_eq_true, nat_blt_eq, nat_ble_eq, decide_eq_true_eq] at h
    exact ⟨⟨h.1.2, h.1.1⟩, h.2⟩

theorem wfEs_mem : ∀ (es : List Ent) (b : Nat), wfEs es b = true → ∀ e ∈ es, EntOK b e
  | [], _, _, e, he => absurd he (List.not_mem_nil)
  | e :: es, b, h, e', he' => by
    obtain ⟨h1, h2⟩ := wfEs_cons h
    rcases List.mem_cons.mp he' with rfl | he'
    · exact h1
    · exact (wfEs_mem es e.node h2 e' he').mono (Nat.le_of_lt h1.node_lt.2)

/-- An entry whose nodes are all below `k` holds under `env'` iff under `env`, when the two agree
below `k`. -/
theorem holds_congr (av : Nat → Nat → Bool) {env env' : Nat → Bool} {k : Nat} {e : Ent}
    (he : EntOK k e) (hag : ∀ j, j < k → env' j = env j) : e.holds av env' ↔ e.holds av env := by
  cases e with
  | gate k' l r =>
    simp only [EntOK] at he
    simp only [Ent.holds]
    rw [hag k' (by omega), lv_congr (hag (l / 2) (by omega)), lv_congr (hag (r / 2) (by omega))]
  | atom k' v i =>
    simp only [EntOK] at he
    simp only [Ent.holds]
    rw [hag k' (by omega)]

theorem envOf_good (av : Nat → Nat → Bool) : ∀ (es : List Ent) (b : Nat), wfEs es b = true →
    envOf av es 0 = false ∧ ∀ e ∈ es, e.holds av (envOf av es)
  | [], _, _ => ⟨rfl, fun _ h => absurd h List.not_mem_nil⟩
  | e :: es, b, h => by
    obtain ⟨h1, h2⟩ := wfEs_cons h
    obtain ⟨ih0, ih1⟩ := envOf_good av es e.node h2
    have hk := h1.node_lt
    -- the new valuation agrees with the old one below `e.node`
    have hag : ∀ j, j < e.node → envOf av (e :: es) j = envOf av es j := by
      intro j hj; simp only [envOf]; rw [if_neg (by omega)]
    refine ⟨by rw [hag 0 (by omega)]; exact ih0, fun e' he' => ?_⟩
    rcases List.mem_cons.mp he' with rfl | he'
    · cases e' with
      | gate k l r =>
        simp only [EntOK] at h1
        have e1 : envOf av (Ent.gate k l r :: es) k = (lv (envOf av es) l && lv (envOf av es) r) := by
          simp [envOf, Ent.node, Ent.value]
        show envOf av (Ent.gate k l r :: es) k =
          (lv (envOf av (Ent.gate k l r :: es)) l && lv (envOf av (Ent.gate k l r :: es)) r)
        rw [lv_congr (hag (l / 2) (by simp [Ent.node]; omega)),
          lv_congr (hag (r / 2) (by simp [Ent.node]; omega)), e1]
      | atom k v i =>
        simp [Ent.holds, envOf, Ent.node, Ent.value]
    · exact (holds_congr av (wfEs_mem es e.node h2 e' he') hag).mpr (ih1 e' he')

/-! ## The CNF -/

theorem litC_sat (env : Nat → Bool) (l : Nat) : (env (litC l).1 == (litC l).2) = lv env l := by
  simp only [litC, lv, nat_beq_eq, cond_decide]
  split <;> cases env (l / 2) <;> simp_all

theorem gateClauses_all (av : Nat → Nat → Bool) (env : Nat → Bool) :
    ∀ (es : List Ent), (∀ e ∈ es, e.holds av env) → ∀ (acc : List (List (Nat × Bool))),
      acc.all (fun c => c.any (fun l => env l.1 == l.2)) = true →
      (gateClauses es acc).all (fun c => c.any (fun l => env l.1 == l.2)) = true
  | [], _, acc, hacc => hacc
  | .atom .. :: es, h, acc, hacc =>
    gateClauses_all av env es (fun e he => h e (List.mem_cons_of_mem _ he)) acc hacc
  | .gate k l r :: es, h, acc, hacc => by
    apply gateClauses_all av env es (fun e he => h e (List.mem_cons_of_mem _ he))
    have hk := h _ (List.mem_cons_self ..)
    simp only [Ent.holds] at hk
    have hn : ∀ x, (env (litC (neg x)).1 == (litC (neg x)).2) = !lv env x := by
      intro x; rw [litC_sat, lv_neg]
    simp only [List.all_cons, List.any_cons, List.any_nil, Bool.or_false, litC_sat, hn, hacc,
      Bool.and_true, hk]
    cases lv env l <;> cases lv env r <;> rfl

theorem cnfOf_all (av : Nat → Nat → Bool) (env : Nat → Bool) (es : List Ent) (out : Nat)
    (h0 : env 0 = false) (h : ∀ e ∈ es, e.holds av env) (ho : lv env out = true) :
    (cnfOf es out).all (fun c => c.any (fun l => env l.1 == l.2)) = true := by
  simp only [cnfOf, List.all_cons, List.any_cons, List.any_nil, Bool.or_false, litC_sat, ho, h0,
    Bool.true_and]
  exact gateClauses_all av env es h [] rfl

/-! ## The theorem -/

/-- **Soundness of the bit-blaster.** If the problem only uses supported constructors, its entries
are well formed, and its CNF is unsatisfiable, then the `bv_decide` problem is unsatisfiable. -/
theorem unsat_of_cnf (bv : BVLogicalExpr) (hs : supportedBool bv = true)
    (hwf : wfEs (blastBool St.empty bv).1.es (blastBool St.empty bv).1.n = true)
    (hcnf : ∀ a : Nat → Bool, (cnfOf (blastBool St.empty bv).1.es (blastBool St.empty bv).2).all
        (fun c => c.any (fun l => a l.1 == l.2)) = false) :
    bv.Unsat := by
  intro assign
  have hspec := blastBool_spec assign bv St.empty hs
  generalize blastBool St.empty bv = p at hspec hwf hcnf
  rcases p with ⟨st, out⟩
  simp only at hwf hcnf hspec
  obtain ⟨h0, hh⟩ := envOf_good (avOf assign) st.es st.n hwf
  have hval := hspec.2 inv_empty (envOf (avOf assign) st.es) ⟨h0, hh⟩
  cases hb : BVLogicalExpr.eval assign bv
  · rfl
  · exfalso
    rw [hb] at hval
    have := cnfOf_all (avOf assign) _ st.es out h0 hh hval
    rw [hcnf] at this
    exact Bool.false_ne_true this

end BVS
