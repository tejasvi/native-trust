import PP12Lrat.Z13Kts.FactsDefs
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


namespace PP12Lrat.Z13Kts

/-- Slice 5 (the first choices `level1[65]`, …, `level1[77]`): the rows of its leaves are the rows `rowStart[5]`, … of `bases_tinf.txt`, and the histogram of the
transversal-class counts of its labelled systems is `sliceHist[5]` (`native_decide`). -/
theorem facts05 : sliceFacts ((level1.drop (13 * 5)).take 13)
    ((fileRows.drop (rowStart.getD 5 0)).take (rowCount.getD 5 0)) = (true, sliceHist.getD 5 []) := by
  kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end PP12Lrat.Z13Kts
