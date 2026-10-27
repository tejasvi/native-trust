import BVS.Sound.Unary
/-!
# Soundness of the bit-blaster: expressions, predicates, Boolean structure

`blastBool_spec`: under every valuation that respects the entries of the final state, the output
literal of `blastBool` has the value of the `bv_decide` problem under the assignment.
-/
namespace BVS
open Std.Tactic.BVDecide

/-- Bit `i` of variable `v` under an assignment. -/
def avOf (assign : BVExpr.Assignment) : Nat → Nat → Bool := fun v i => (assign.get v).bv.getLsbD i

theorem bitsOf_var {w : Nat} (assign : BVExpr.Assignment) (v : Nat) :
    (List.range w).map (avOf assign v) = bitsOf ((assign.get v).bv.truncate w) := by
  rw [bitsOf, bitsFrom, List.range_eq_range']
  apply List.map_congr_left
  intro j hj
  simp only [List.mem_range'] at hj
  simp [avOf, BitVec.truncate_eq_setWidth, show j < w by omega]

theorem len_of_map {f : Nat → Bool} {xs : List Nat} {l : List Bool} (h : xs.map f = l) :
    xs.length = l.length := by rw [← h, List.length_map]

theorem binSemC_bitsOf {w : Nat} (op : BVBinOp) (x y : BitVec w) :
    binSemC (opCode op) (bitsOf x) (bitsOf y) = bitsOf (op.eval x y) := by
  cases op with
  | and => exact bitsOf_and x y
  | or => exact bitsOf_or x y
  | xor => exact bitsOf_xor x y
  | add => exact addL_bitsOf_false x y
  | mul => simp only [binSemC, opCode, length_bitsOf]; exact mul_bitsOf x y
  | udiv => simp only [binSemC, opCode, length_bitsOf]; exact udiv_bitsOf x y
  | umod => simp only [binSemC, opCode, length_bitsOf]; exact umod_bitsOf x y

theorem blastBin_bv_spec (assign : BVExpr.Assignment) {w : Nat} (op : BVBinOp) (st : St) (xs ys : List Nat)
    (x y : BitVec w) :
    Spec (avOf assign) st (blastBin op st xs ys) (fun env r =>
      xs.map (lv env) = bitsOf x → ys.map (lv env) = bitsOf y → r.map (lv env) = bitsOf (op.eval x y)) :=
  (blastBin_spec op st xs ys).weaken fun env r _ H hx hy => by
    have hl : ys.length = xs.length := by rw [len_of_map hx, len_of_map hy, length_bitsOf, length_bitsOf]
    rw [H hl, hx, hy, binSemC_bitsOf]

theorem blastExpr_spec (assign : BVExpr.Assignment) {w : Nat} (e : BVExpr w) :
    ∀ (st : St), supported e = true →
      Spec (avOf assign) st (blastExpr st e) (fun env r => r.map (lv env) = bitsOf (e.eval assign)) := by
  induction e with
  | var v =>
    intro st _
    simp only [blastExpr]
    exact (blastVar_spec st v _).weaken fun env r _ H => by rw [H, bitsOf_var, BVExpr.eval_var]
  | const val =>
    intro st _
    simp only [blastExpr]
    exact Spec.ret fun env g => by rw [bitsOf_const env g.1, BVExpr.eval_const]
  | extract start len e ih =>
    intro st hs
    simp only [supported] at hs
    simp only [blastExpr]
    rcases h1 : blastExpr st e with ⟨st1, xs⟩
    have s1 := h1 ▸ ih st hs
    dsimp only
    exact Spec.bind s1 (Spec.ret fun env g H => by
      rw [map_takeD env g.1, List.map_drop, H, bitsOf_extract, BVExpr.eval_extract])
  | bin x op y ihx ihy =>
    intro st hs
    simp only [supported, Bool.and_eq_true] at hs
    simp only [blastExpr]
    rcases h1 : blastExpr st x with ⟨st1, xs⟩
    have s1 := h1 ▸ ihx st hs.1
    dsimp only
    rcases h2 : blastExpr st1 y with ⟨st2, ys⟩
    have s2 := h2 ▸ ihy st1 hs.2
    dsimp only
    exact Spec.bind s1 (Spec.bind s2 ((blastBin_bv_spec assign op st2 xs ys (x.eval assign) (y.eval assign)).weaken
      fun env r _ H Hy Hx => by rw [H Hx Hy, BVExpr.eval_bin]))
  | un op x ih =>
    intro st hs
    simp only [supported, Bool.and_eq_true] at hs
    simp only [blastExpr]
    rcases h1 : blastExpr st x with ⟨st1, xs⟩
    have s1 := h1 ▸ ih st hs.2
    dsimp only
    exact Spec.bind s1 ((blastUn_spec (av := avOf assign) op st1 xs (x.eval assign)).weaken
      fun env r _ H Hx => by rw [H Hx, BVExpr.eval_un])
  | append x y h ihx ihy =>
    intro st hs
    subst h
    simp only [supported, Bool.and_eq_true] at hs
    simp only [blastExpr]
    rcases h1 : blastExpr st x with ⟨st1, xs⟩
    have s1 := h1 ▸ ihx st hs.1
    dsimp only
    rcases h2 : blastExpr st1 y with ⟨st2, ys⟩
    have s2 := h2 ▸ ihy st1 hs.2
    dsimp only
    exact Spec.bind s1 (Spec.bind s2 (Spec.ret fun env g Hy Hx => by
      rw [List.map_append, Hx, Hy, bitsOf_append, BVExpr.eval_append]))
  | replicate n x h ih =>
    intro st hs
    subst h
    simp only [supported] at hs
    simp only [blastExpr]
    rcases h1 : blastExpr st x with ⟨st1, xs⟩
    have s1 := h1 ▸ ih st hs
    dsimp only
    refine Spec.bind s1 (Spec.ret fun env g H => ?_)
    rw [BVExpr.eval_replicate, List.map_flatten, List.map_replicate, H, replicate_bitsOf]
  | shiftLeft x y ihx ihy =>
    intro st hs
    simp only [supported, Bool.and_eq_true] at hs
    simp only [blastExpr]
    rcases h1 : blastExpr st x with ⟨st1, xs⟩
    have s1 := h1 ▸ ihx st hs.1
    dsimp only
    rcases h2 : blastExpr st1 y with ⟨st2, ys⟩
    have s2 := h2 ▸ ihy st1 hs.2
    dsimp only
    refine Spec.bind s1 (Spec.bind s2 ((barrel_spec shlC shlL length_shlC map_shlC ys st2 xs 0).weaken
      fun env r _ H Hy Hx => ?_))
    rw [H, Hx, Hy, BVExpr.eval_shiftLeft, BitVec.shiftLeft_eq']
    have := barrelL_bitsOf (fun a => x.eval assign <<< a) shlL
      (fun a k => by rw [shlL_bitsOf, BitVec.shiftLeft_add]) (y.eval assign)
    simp only [BitVec.shiftLeft_zero] at this
    exact this
  | shiftRight x y ihx ihy =>
    intro st hs
    simp only [supported, Bool.and_eq_true] at hs
    simp only [blastExpr]
    rcases h1 : blastExpr st x with ⟨st1, xs⟩
    have s1 := h1 ▸ ihx st hs.1
    dsimp only
    rcases h2 : blastExpr st1 y with ⟨st2, ys⟩
    have s2 := h2 ▸ ihy st1 hs.2
    dsimp only
    refine Spec.bind s1 (Spec.bind s2 ((barrel_spec shrC shrL length_shrC map_shrC ys st2 xs 0).weaken
      fun env r _ H Hy Hx => ?_))
    rw [H, Hx, Hy, BVExpr.eval_shiftRight, BitVec.ushiftRight_eq']
    have := barrelL_bitsOf (fun a => x.eval assign >>> a) shrL
      (fun a k => by rw [shrL_bitsOf, BitVec.shiftRight_add]) (y.eval assign)
    simp only [BitVec.ushiftRight_zero] at this
    exact this
  | arithShiftRight x y ihx ihy =>
    intro st hs
    simp only [supported, Bool.and_eq_true] at hs
    simp only [blastExpr]
    rcases h1 : blastExpr st x with ⟨st1, xs⟩
    have s1 := h1 ▸ ihx st hs.1
    dsimp only
    rcases h2 : blastExpr st1 y with ⟨st2, ys⟩
    have s2 := h2 ▸ ihy st1 hs.2
    dsimp only
    refine Spec.bind s1 (Spec.bind s2 ((barrel_spec sarC sarL length_sarC map_sarC ys st2 xs 0).weaken
      fun env r _ H Hy Hx => ?_))
    rw [H, Hx, Hy, BVExpr.eval_arithShiftRight, BitVec.sshiftRight_eq']
    have := barrelL_bitsOf (fun a => (x.eval assign).sshiftRight a) sarL
      (fun a k => by rw [sarL_bitsOf, BitVec.sshiftRight_add]) (y.eval assign)
    simp only [BitVec.sshiftRight_zero] at this
    exact this

theorem blastPred_spec (assign : BVExpr.Assignment) (p : BVPred) (st : St) (hs : supportedPred p = true) :
    Spec (avOf assign) st (blastPred st p) (fun env r => lv env r = p.eval assign) := by
  cases p with
  | bin x op y =>
    simp only [supportedPred, Bool.and_eq_true] at hs
    simp only [blastPred]
    rcases h1 : blastExpr st x with ⟨st1, xs⟩
    have s1 := h1 ▸ blastExpr_spec assign x st hs.1
    dsimp only
    rcases h2 : blastExpr st1 y with ⟨st2, ys⟩
    have s2 := h2 ▸ blastExpr_spec assign y st1 hs.2
    dsimp only
    cases op with
    | eq =>
      exact Spec.bind s1 (Spec.bind s2 ((blastEq_spec st2 xs ys).weaken fun env r _ H Hy Hx => by
        rw [H, Hx, Hy, eq_bitsOf, BVPred.eval_bin]; rfl))
    | ult =>
      exact Spec.bind s1 (Spec.bind s2 ((blastUlt_spec st2 xs ys).weaken fun env r _ H Hy Hx => by
        rw [H, Hx, Hy, ult_bitsOf, BVPred.eval_bin]; rfl))
  | getLsbD e i =>
    simp only [supportedPred] at hs
    simp only [blastPred]
    rcases h1 : blastExpr st e with ⟨st1, xs⟩
    have s1 := h1 ▸ blastExpr_spec assign e st hs
    dsimp only
    exact Spec.bind s1 (Spec.ret fun env g H => by
      rw [getD_map_lv env g.1, H, getD_bitsOf, BVPred.eval_getLsbD])

theorem gateOf_spec (av : Nat → Nat → Bool) (g : Gate) (st : St) (a b : Nat) :
    Spec av st (gateOf g st a b) (fun env r => lv env r = g.eval (lv env a) (lv env b)) := by
  cases g with
  | and => exact mkAnd_spec av st a b
  | or => exact mkOr_spec st a b
  | xor => exact mkXor_spec st a b
  | beq => exact mkXnor_spec st a b

theorem blastBool_spec (assign : BVExpr.Assignment) (b : BVLogicalExpr) :
    ∀ (st : St), supportedBool b = true →
      Spec (avOf assign) st (blastBool st b) (fun env r => lv env r = b.eval assign) := by
  induction b with
  | literal p =>
    intro st hs
    simp only [supportedBool] at hs
    simp only [blastBool]
    exact (blastPred_spec assign p st hs).weaken fun env r _ H => by rw [H]; rfl
  | const c =>
    intro st _
    simp only [blastBool]
    exact Spec.ret fun env g => by cases c <;> simp [g.lv0, g.lv1, BVLogicalExpr.eval]
  | not x ih =>
    intro st hs
    simp only [supportedBool] at hs
    simp only [blastBool]
    rcases h1 : blastBool st x with ⟨st1, l⟩
    have s1 := h1 ▸ ih st hs
    dsimp only
    exact Spec.bind s1 (Spec.ret fun env g H => by rw [lv_neg, H]; rfl)
  | gate g x y ihx ihy =>
    intro st hs
    simp only [supportedBool, Bool.and_eq_true] at hs
    simp only [blastBool]
    rcases h1 : blastBool st x with ⟨st1, a⟩
    have s1 := h1 ▸ ihx st hs.1
    dsimp only
    rcases h2 : blastBool st1 y with ⟨st2, b⟩
    have s2 := h2 ▸ ihy st1 hs.2
    dsimp only
    exact Spec.bind s1 (Spec.bind s2 ((gateOf_spec _ g st2 a b).weaken fun env r _ H Hb Ha => by
      rw [H, Ha, Hb]; rfl))
  | ite c x y ihc ihx ihy =>
    intro st hs
    simp only [supportedBool, Bool.and_eq_true] at hs
    simp only [blastBool]
    rcases h1 : blastBool st c with ⟨st1, l⟩
    have s1 := h1 ▸ ihc st hs.1.1
    dsimp only
    rcases h2 : blastBool st1 x with ⟨st2, a⟩
    have s2 := h2 ▸ ihx st1 hs.1.2
    dsimp only
    rcases h3 : blastBool st2 y with ⟨st3, b⟩
    have s3 := h3 ▸ ihy st2 hs.2
    dsimp only
    exact Spec.bind s1 (Spec.bind s2 (Spec.bind s3 ((mkMux_spec st3 l a b).weaken
      fun env r _ H Hb Ha Hc => by rw [H, Hc, Ha, Hb]; rfl)))

end BVS
