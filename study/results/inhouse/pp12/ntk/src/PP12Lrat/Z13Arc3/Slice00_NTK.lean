import PP12Lrat.Z13ArcDefs
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace PP12Lrat.Z13Arc

/-- Slice 0 of the degree-3 search: the first choice `sysLevel1[0]` of `sysSearch`. Below it there are 2360 leaves, and
`check3` accepts every one of them (`native_decide`). -/
theorem slice3_00 : sliceStat3 0 = (2360, true) := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end PP12Lrat.Z13Arc
