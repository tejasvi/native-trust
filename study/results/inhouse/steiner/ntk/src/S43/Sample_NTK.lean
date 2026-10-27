import S43.Sound.Data
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


/-! Sample module, not part of the release: the facts of `S43Final.lean` and of the four `S43Data/Ck/Case.lean`
modules that need no data file (the table checks `sizes_st` and `sizes_reg`, and the monotonicity checks of the four
cases), with their statements copied unchanged. -/

namespace S43.Sample
open S43

theorem sizes_st : sizeCheck .st = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem sizes_reg : sizeCheck .reg = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem mono_c1 : monoCheck .reg 3 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem mono_c2 : monoCheck .st 2 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem mono_c3 : monoCheck .reg 1 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })
theorem mono_c4 : monoCheck .st 1 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end S43.Sample
