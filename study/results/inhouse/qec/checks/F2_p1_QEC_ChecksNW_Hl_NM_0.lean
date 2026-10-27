import NativeTrust
import QEC.ChecksNW.Hl.NM
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth QEC.ChecksNW.Hl.NM 0 (config := { split := 8, trace := true })
