import BVS
import Examples.ShardFacts
/-!
# Example: sharded conversion

Build the facts first (`lake build Examples.ShardFacts`), then run
`scripts/shard.sh prep/ShardPrep.lean <work dir> 2`. Compiling this file runs the SAT solver, proves
the base checks, and writes `ShardPrep_S0.lean`, `ShardPrep_S1.lean` (the LRAT chunks, dealt
round-robin) and `ShardPrep_Final.lean` into the current directory (the work directory). The final
module proves `bvs5fact_0.unsat`, `bvs5fact_1.unsat` and rebuilds `shard_mul_three` and
`shard_and_or` as `bvs5_<k>` with their original statements.
-/

bvs5_list Examples.ShardFacts
bvs5_prep Examples.ShardFacts "." 2 0 1
