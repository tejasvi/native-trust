import RCert.M3G.Data
import RCert.M3G.TeffLit
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


/-!
# M3 at period 27720 (U3g/V4g modulus), N version: the native checks (precompiled library, compiled `native_decide`)
-/

namespace R45.M3G

open R45.M3 hiding PER accG sumDvd certOK ellPs mkBD prC drC tbC teffOf bsOf teffD

theorem certOK_data : certOK D.data = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem sumsOK_data : sumsOK D.data (runDP tab0 D.data.gA) = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem teffD_eq : teffD D.data = teffLit := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem R0tD_eq : R0tD D.data = R0tLit := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end R45.M3G
