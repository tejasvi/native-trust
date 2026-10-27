import Examples.GroupA
/-!
Second module of the group example (`Examples/Group.lean`): one fact proved by `bv_decide`, and a theorem
that uses the facts of both modules.
-/

theorem gb_and_or (x y : BitVec 8) : (x &&& y) + (x ||| y) = x + y := by bv_decide

theorem gb_both (x y : BitVec 8) : x * 3 = x + x + x ∧ (x &&& y) + (x ||| y) = x + y :=
  ⟨ga_mul_three x, gb_and_or x y⟩
