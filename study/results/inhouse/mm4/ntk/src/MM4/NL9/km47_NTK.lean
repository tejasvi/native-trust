import MM4.LeafN
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace MM4

set_option maxHeartbeats 0 in
/-- The leaf-only run of `km47` to depth 9 (native evaluation, one parallel task per unpruned 4-prefix). -/
theorem km47_runNL9 : runN (relabel km47 km47Ord) km47Auts 9 4 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem km47_ordLenNL9 : km47Ord.length = km47.length := by decide +kernel
theorem km47_ordInvNL9 : ∀ t < km47.length, km47Inv.getD t 0 < km47.length ∧ km47Ord.getD (km47Inv.getD t 0) 0 = t := by
  decide +kernel
theorem km47_rmasks16NL9 : masks16 (relabel km47 km47Ord) = true := by decide +kernel
theorem km47_rnonzeroNL9 : nonzeroFacs (relabel km47 km47Ord) = true := by decide +kernel
theorem km47_autOKNL9 : km47Auts.all (autOK (relabel km47 km47Ord)) = true := by decide +kernel

/-- **Local optimality of `km47` to depth 9** (native track, leaf-only run). -/
theorem km47_localOptNL9 : LocalOpt km47 9 :=
  localOpt_of_runN km47 km47Ord km47Inv km47Auts 9 4 (by norm_num) (by norm_num) (by decide) km47_ordLenNL9 (by decide)
    km47_ordInvNL9 km47_rmasks16NL9 km47_rnonzeroNL9 km47_autOKNL9 km47_runNL9

end MM4
