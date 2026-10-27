import RCert.G.BLit
import RCert.M3G.TeffLit
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


/-! U3g/V4g, N version: the divisor form of the M3 table (native check, precompiled library). -/

namespace R45.U3G

theorem tabB_BLit_eq : tabB BLit = (List.range 27720).map fun c =>
    R45.M3G.teffLit.getD c 0 - ((Nat.gcd c 27720 : Nat) : Rat) * R45.M3G.R0tLit := by
  kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end R45.U3G
