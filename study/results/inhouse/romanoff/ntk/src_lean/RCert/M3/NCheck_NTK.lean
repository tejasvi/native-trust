import RCert.M3.Data
import RCert.M3.TeffLit
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


/-!
# M3, N version: the native checks (precompiled library, so `native_decide` runs compiled code)
-/

namespace R45.M3

theorem certOK_data : certOK D.data = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem sumsOK_data : sumsOK D.data (runDP tab0 D.data.gA) = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem teffD_eq : teffD D.data = teffLit := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end R45.M3
