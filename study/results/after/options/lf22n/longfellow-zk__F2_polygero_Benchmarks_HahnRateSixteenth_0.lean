import NativeTrust
import polygero.Benchmarks.HahnRateSixteenth
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth polygero.Benchmarks.HahnRateSixteenth 0 (config := { propSplit := true, split := 16, trace := true })
