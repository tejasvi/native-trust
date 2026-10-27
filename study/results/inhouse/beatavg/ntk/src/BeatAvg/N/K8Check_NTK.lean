import BeatAvg.Data.K8
import NativeTrust


/-! Native evaluation of the k = 8 check. -/

open BeatAvg.Check BeatAvg.Data.K8 in
theorem BeatAvg.N.K8.check_ok : checkK8 levels lower mid excl8 lamN lamD den7 qscale = true := by kdecide (config := { native := false, split := 8 })
