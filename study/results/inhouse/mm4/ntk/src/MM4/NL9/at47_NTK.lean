import MM4.LeafN
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace MM4

set_option maxHeartbeats 0 in
/-- The leaf-only run of `at47` to depth 9 (native evaluation, one parallel task per unpruned 4-prefix). -/
theorem at47_runNL9 : runN (relabel at47 at47Ord) at47Auts 9 4 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem at47_ordLenNL9 : at47Ord.length = at47.length := by decide +kernel
theorem at47_ordInvNL9 : ∀ t < at47.length, at47Inv.getD t 0 < at47.length ∧ at47Ord.getD (at47Inv.getD t 0) 0 = t := by
  decide +kernel
theorem at47_rmasks16NL9 : masks16 (relabel at47 at47Ord) = true := by decide +kernel
theorem at47_rnonzeroNL9 : nonzeroFacs (relabel at47 at47Ord) = true := by decide +kernel
theorem at47_autOKNL9 : at47Auts.all (autOK (relabel at47 at47Ord)) = true := by decide +kernel

/-- **Local optimality of `at47` to depth 9** (native track, leaf-only run). -/
theorem at47_localOptNL9 : LocalOpt at47 9 :=
  localOpt_of_runN at47 at47Ord at47Inv at47Auts 9 4 (by norm_num) (by norm_num) (by decide) at47_ordLenNL9 (by decide)
    at47_ordInvNL9 at47_rmasks16NL9 at47_rnonzeroNL9 at47_autOKNL9 at47_runNL9

end MM4
