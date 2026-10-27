import Std.Tactic.BVDecide
/-!
# Facts for the sharding example

Proved here by `bv_decide`; `prep/ShardPrep.lean` re-proves both in shards. Their indices among the
module's `bv_decide` axioms are `0` and `1` (`bvs5_list Examples.ShardFacts` prints them).
-/

theorem shard_mul_three (x : BitVec 64) : x * 3 = x + x + x := by bv_decide
theorem shard_and_or (x y : BitVec 256) : (x &&& y) + (x ||| y) = x + y := by bv_decide
