import NativeTrust
import IChO2026Problems.problem_icho_2026_t8_a6
import F2_IChO2026Problems_problem_icho_2026_t8_a6_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth IChO2026Problems.problem_icho_2026_t8_a6 0 (config := { split := 8, trace := true })
