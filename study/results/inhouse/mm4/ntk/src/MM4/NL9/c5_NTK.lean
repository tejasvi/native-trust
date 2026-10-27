import MM4.LeafN
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace MM4

set_option maxHeartbeats 0 in
/-- The leaf-only run of `c5` to depth 9 (native evaluation, one parallel task per unpruned 4-prefix). -/
theorem c5_runNL9 : runN (relabel c5 c5Ord) c5Auts 9 4 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem c5_ordLenNL9 : c5Ord.length = c5.length := by decide +kernel
theorem c5_ordInvNL9 : ∀ t < c5.length, c5Inv.getD t 0 < c5.length ∧ c5Ord.getD (c5Inv.getD t 0) 0 = t := by
  decide +kernel
theorem c5_rmasks16NL9 : masks16 (relabel c5 c5Ord) = true := by decide +kernel
theorem c5_rnonzeroNL9 : nonzeroFacs (relabel c5 c5Ord) = true := by decide +kernel
theorem c5_autOKNL9 : c5Auts.all (autOK (relabel c5 c5Ord)) = true := by decide +kernel

/-- **Local optimality of `c5` to depth 9** (native track, leaf-only run). -/
theorem c5_localOptNL9 : LocalOpt c5 9 :=
  localOpt_of_runN c5 c5Ord c5Inv c5Auts 9 4 (by norm_num) (by norm_num) (by decide) c5_ordLenNL9 (by decide)
    c5_ordInvNL9 c5_rmasks16NL9 c5_rnonzeroNL9 c5_autOKNL9 c5_runNL9

end MM4
