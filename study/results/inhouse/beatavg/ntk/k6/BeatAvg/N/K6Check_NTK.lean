import BeatAvg.Data.K6
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


/-! Native evaluation of the k = 6 check. -/

theorem BeatAvg.N.K6.check_ok : BeatAvg.Data.K6.check = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
