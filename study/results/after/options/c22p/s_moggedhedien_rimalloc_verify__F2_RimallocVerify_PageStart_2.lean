import NativeTrust
import RimallocVerify.PageStart
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth RimallocVerify.PageStart 2 (config := { stage := true, csimp := true, propSplit := true, split := 16, trace := true })
