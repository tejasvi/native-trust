import NativeTrust
import QEC.ChecksNS.S8.NM
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth QEC.ChecksNS.S8.NM 0 (config := { split := 8, trace := true })
