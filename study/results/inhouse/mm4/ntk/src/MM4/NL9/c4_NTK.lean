import MM4.LeafN
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace MM4

set_option maxHeartbeats 0 in
/-- The leaf-only run of `c4` to depth 9 (native evaluation, one parallel task per unpruned 4-prefix). -/
theorem c4_runNL9 : runN (relabel c4 c4Ord) c4Auts 9 4 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem c4_ordLenNL9 : c4Ord.length = c4.length := by decide +kernel
theorem c4_ordInvNL9 : ∀ t < c4.length, c4Inv.getD t 0 < c4.length ∧ c4Ord.getD (c4Inv.getD t 0) 0 = t := by
  decide +kernel
theorem c4_rmasks16NL9 : masks16 (relabel c4 c4Ord) = true := by decide +kernel
theorem c4_rnonzeroNL9 : nonzeroFacs (relabel c4 c4Ord) = true := by decide +kernel
theorem c4_autOKNL9 : c4Auts.all (autOK (relabel c4 c4Ord)) = true := by decide +kernel

/-- **Local optimality of `c4` to depth 9** (native track, leaf-only run). -/
theorem c4_localOptNL9 : LocalOpt c4 9 :=
  localOpt_of_runN c4 c4Ord c4Inv c4Auts 9 4 (by norm_num) (by norm_num) (by decide) c4_ordLenNL9 (by decide)
    c4_ordInvNL9 c4_rmasks16NL9 c4_rnonzeroNL9 c4_autOKNL9 c4_runNL9

end MM4
