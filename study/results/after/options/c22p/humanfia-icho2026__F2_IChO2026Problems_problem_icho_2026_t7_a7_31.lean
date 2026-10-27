import NativeTrust
import IChO2026Problems.problem_icho_2026_t7_a7
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth IChO2026Problems.problem_icho_2026_t7_a7 31 (config := { stage := true, csimp := true, propSplit := true, split := 16, trace := true })
