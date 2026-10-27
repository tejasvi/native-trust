import Std.Tactic.BVDecide
/-! Scaling benchmark for the split base check: `(x &&& y) + (x ||| y) = x + y` at 16384 bits (core `bv_decide`). -/
set_option maxRecDepth 100000
theorem andor_16384 (x y : BitVec 16384) : (x &&& y) + (x ||| y) = x + y := by bv_decide (config := { timeout := 3000 })
