import Char2Comp.CT25
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! (C1), key injectivity and (C2)+(C3) with the integral link criterion for ctrunc(25,13), hole type z4a0. -/
namespace Char2
theorem CT25z4a0_checkC1 : checkC1 CT25z4a0 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem CT25z4a0_checkInj : checkInj CT25z4a0 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem CT25z4a0_checkC23 : checkC23 CT25z4a0 0 1 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
end Char2
