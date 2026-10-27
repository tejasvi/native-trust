import RCert.G.Ev
import NativeTrust
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000


/-!
# U3g/V4g stage 2: the native evaluation (the only `native_decide` of stage 2)

`finalOK 123 = decide (claimU ≤ VU acc) && decide (claimV ≤ VV acc)`, `acc = evalPar 123 (foldOrbits 120 baseP)`: the BASE
keys in pieces of 123 (64 pieces), one dedicated task per piece (any piece size gives the same value, `Vf_evalPar`).  One
evaluation serves both bounds.  This module imports only the compiled evaluator; it is elaborated once, on a large machine,
and its `.olean` is reused.
-/

namespace Romanoff.G.S2

open R45 R45.EVG

theorem finalOK_true : finalOK 123 = true := by kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })

end Romanoff.G.S2
