import BVS
import Examples.SplitFacts
/-!
# Example: split base check

Build the fact first (`lake build Examples.SplitFacts`), then run
`scripts/shard.sh prep/SplitPrep.lean <work dir> 2`. Compiling this file runs the SAT solver and writes
two shard files and `SplitPrep_Final.lean` into the current directory. The shards prove the
bit-blaster's run (`bvs6_blast`), one `segOK` theorem per segment of 2000 nodes (`bvs6_seg`) and the
LRAT chunks; the final module assembles `bvs6fact_0.unsat` with `BVS.bvs_unsat5` and rebuilds
`split_and_or` as `bvs6_1`.
-/

bvs6_prep Examples.SplitFacts "." 2 2000 0
