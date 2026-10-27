import Char2Comp.CT25
import Char2Comp.Extra
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! Every NS edge of ctrunc(25, 13) is available, for each of the five hole types, by `native_decide`. -/
namespace Char2
theorem CT25z8a0_checkNSAvail : checkNSAvail CT25z8a0 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem CT25z8a1_checkNSAvail : checkNSAvail CT25z8a1 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem CT25z8a2_checkNSAvail : checkNSAvail CT25z8a2 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem CT25z4a0_checkNSAvail : checkNSAvail CT25z4a0 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem CT25z4a1_checkNSAvail : checkNSAvail CT25z4a1 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
end Char2
