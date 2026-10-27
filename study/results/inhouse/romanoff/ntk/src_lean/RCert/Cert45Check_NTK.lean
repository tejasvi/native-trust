import RCert.Cert45
import RCert.M3.TeffLit
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


/-! The certificate values at the M3 table `teffLit` (compiled `native_decide`, precompiled library):
U2 (`c1 = 8`, `mu = 0`) clears 0.109406 and v3 (`c1 = C1v3`, `mu = muV3`) clears 0.117953. -/

open R45 R45.D45 R45.P45

namespace R45.P45

theorem cert_U2_lit : (109406 / 1000000 : Rat) ≤ lagBound (parOf R45.M3.teffLit 8 0) (orbits 120 (ellPO.map (·.1))) := by
  kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

theorem cert_v3_lit :
    (117953 / 1000000 : Rat) ≤ lagBound (parOf R45.M3.teffLit C1v3 muV3) (orbits 120 (ellPO.map (·.1))) := by
  kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end R45.P45
