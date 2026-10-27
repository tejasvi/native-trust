import MM4.LeafN
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace MM4

set_option maxHeartbeats 0 in
/-- The leaf-only run of `c3` to depth 9 (native evaluation, one parallel task per unpruned 4-prefix). -/
theorem c3_runNL9 : runN (relabel c3 c3Ord) c3Auts 9 4 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem c3_ordLenNL9 : c3Ord.length = c3.length := by decide +kernel
theorem c3_ordInvNL9 : ∀ t < c3.length, c3Inv.getD t 0 < c3.length ∧ c3Ord.getD (c3Inv.getD t 0) 0 = t := by
  decide +kernel
theorem c3_rmasks16NL9 : masks16 (relabel c3 c3Ord) = true := by decide +kernel
theorem c3_rnonzeroNL9 : nonzeroFacs (relabel c3 c3Ord) = true := by decide +kernel
theorem c3_autOKNL9 : c3Auts.all (autOK (relabel c3 c3Ord)) = true := by decide +kernel

/-- **Local optimality of `c3` to depth 9** (native track, leaf-only run). -/
theorem c3_localOptNL9 : LocalOpt c3 9 :=
  localOpt_of_runN c3 c3Ord c3Inv c3Auts 9 4 (by norm_num) (by norm_num) (by decide) c3_ordLenNL9 (by decide)
    c3_ordInvNL9 c3_rmasks16NL9 c3_rnonzeroNL9 c3_autOKNL9 c3_runNL9

end MM4
