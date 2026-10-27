import Std.Tactic.BVDecide
/-! First module of the group example (`Examples/Group.lean`): one fact proved by `bv_decide`. -/

theorem ga_mul_three (x : BitVec 8) : x * 3 = x + x + x := by bv_decide
