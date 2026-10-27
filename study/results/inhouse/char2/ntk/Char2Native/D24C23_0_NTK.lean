import Char2Comp
import Char2Comp.Route
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000

/-! (C2) + (C3) with the integral link criterion, and the route structure and window types (H₂₄), for the NS edges
of D₂₄ with code ≡ 0 (mod 8), by `native_decide`. -/
namespace Char2
theorem D24_checkC23H_0 : checkC23H D24 D24endPath 0 8 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem D24_checkC23_0 : checkC23 D24 0 8 = true := checkC23_of_checkC23H D24_checkC23H_0
end Char2
