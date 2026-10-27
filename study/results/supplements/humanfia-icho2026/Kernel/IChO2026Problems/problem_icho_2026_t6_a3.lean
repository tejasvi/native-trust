import NativeTrust
import IChO2026Problems.problem_icho_2026_t6_a3
import F2_IChO2026Problems_problem_icho_2026_t6_a3_0
import F2_IChO2026Problems_problem_icho_2026_t6_a3_1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth IChO2026Problems.problem_icho_2026_t6_a3 0 (config := { split := 8, trace := true })
trust_check_nth IChO2026Problems.problem_icho_2026_t6_a3 1 (config := { split := 8, trace := true })
