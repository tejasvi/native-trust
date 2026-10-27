import Char2Comp
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! (C1), key injectivity, the (C1) statistics and the far-from-NS facts for D₂₄, by `native_decide`. -/
namespace Char2
theorem D24_checkC1 : checkC1 D24 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem D24_checkInj : checkInj D24 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem D24_stats : c1Stats D24 = D24stats := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem D24_checkFar : checkFar D24 (D24lane ++ D24endPath) = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
end Char2
