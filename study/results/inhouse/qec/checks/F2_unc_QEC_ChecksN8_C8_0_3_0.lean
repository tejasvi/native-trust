import NativeTrust
import QEC.ChecksN8.C8_0_3
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth QEC.ChecksN8.C8_0_3 0 (config := { split := 8, trace := true })
