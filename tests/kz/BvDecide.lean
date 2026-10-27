import NativeTrust
import Std.Tactic.BVDecide

/-! `bv_decide` facts: the axiom asserts that the compiled LRAT checker accepts the certificate. -/

theorem bv_add_zero (x : BitVec 8) : x + 0#8 = x := by bv_decide

theorem bv_xor_self (x y : BitVec 16) : (x ^^^ y) ^^^ y = x := by bv_decide

#print axioms bv_xor_self
#kernel_blockers bv_xor_self
trust_check bv_add_zero
trust_check bv_xor_self
