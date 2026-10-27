import PP12Lrat.Z13Design.FactsDefs
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace PP12Lrat.Z13Design

/-- Slice 0 of the first branching (the first choice `sysLevel1[0]`): the statistics of its leaves are `sliceExp[0]`
(`native_decide`). -/
theorem facts00 : sliceStats ((sysLevel1.drop 0).take 1) = sliceExp.getD 0 default := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end PP12Lrat.Z13Design
