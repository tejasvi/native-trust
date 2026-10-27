import NativeTrust
import QEC.ChecksN.N_Z_9
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth QEC.ChecksN.N_Z_9 5 (config := { split := 8, trace := true })
