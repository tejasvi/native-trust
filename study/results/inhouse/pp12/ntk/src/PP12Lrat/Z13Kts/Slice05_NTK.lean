import PP12Lrat.Z13KtsCore
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace PP12Lrat.Z13Kts

/-- Slice 5 of the first branching: the first choices `level1[65]`, …, `level1[77]`. `checkLeaf` accepts every leaf below them (`native_decide`). -/
theorem slice05 : ((level1.drop (13 * 5)).take 13).all branchOK = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end PP12Lrat.Z13Kts
