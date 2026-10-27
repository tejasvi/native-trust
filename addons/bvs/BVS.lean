module

public import BVS.Driver.Split
public import BVS.Driver.Group
public import BVS.Tactic
public import BVS.Estimate
/-!
# BVS: kernel-checked re-proofs of `bv_decide` facts

Importing `BVS` provides the commands of `BVS.Driver.Core` (`bvs4_kernelize`, `bvs4_module`,
`bvs4_prep_module`, `bvs4_chunk`, `bvs4_assemble_module`), `BVS.Driver.Select` (`bvs5_list`,
`bvs5_prep`, `bvs5_assemble`, `bvs5_fact`), `BVS.Driver.Split` (`bvs6_prep`, `bvs6_blast`,
`bvs6_seg`, `bvs6_assemble`) and `BVS.Driver.Group` (`bvs5_group`), the tactic `bv_kdecide` of
`BVS.Tactic` (proves `bv_decide` goals with kernel-checked proofs), the cost estimate `bvs5_estimate` of
`BVS.Estimate`, and the soundness theorems behind
them (`BVS.bvs_unsat4`, `BVS.bvs_unsat5` and the lemmas they use). See `README.md`.
-/
