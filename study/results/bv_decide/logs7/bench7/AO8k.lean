import Std.Tactic.BVDecide
/-! Scaling benchmark for the split base check: `(x &&& y) + (x ||| y) = x + y` at 8192 bits (core `bv_decide`). -/
set_option maxRecDepth 100000
theorem andor_8192 (x y : BitVec 8192) : (x &&& y) + (x ||| y) = x + y := by bv_decide (config := { timeout := 3000 })
