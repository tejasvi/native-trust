import BeatAvg.Data.K7
import NativeTrust


/-! Native evaluation of the k = 7 check. -/

theorem BeatAvg.N.K7.check_ok : BeatAvg.Data.K7.check = true := by kdecide (config := { native := false, split := 8 })
