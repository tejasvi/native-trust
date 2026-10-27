import NativeTrust
import IChO2026Problems.problem_icho_2026_t3_a5
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth IChO2026Problems.problem_icho_2026_t3_a5 36 (config := { split := 8, trace := true })
