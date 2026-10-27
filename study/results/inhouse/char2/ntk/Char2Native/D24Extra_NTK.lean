import Char2Comp.D24
import Char2Comp.Extra
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! Every NS edge of D₂₄ is available, by `native_decide`. -/
namespace Char2
theorem D24_checkNSAvail : checkNSAvail D24 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
end Char2
