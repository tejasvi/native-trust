import NativeTrust
import QEC.ChecksNW.H2.Tab
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth QEC.ChecksNW.H2.Tab 0 (config := { split := 8, trace := true })
