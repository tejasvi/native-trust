import Std.Tactic.BVDecide
/-!
# A fact for the split-base-check example

Proved here by `bv_decide`; `prep/SplitPrep.lean` re-proves it with the base check split into the
bit-blaster's run and segments of 2000 nodes.
-/

theorem split_and_or (x y : BitVec 256) : (x &&& y) + (x ||| y) = x + y := by bv_decide
