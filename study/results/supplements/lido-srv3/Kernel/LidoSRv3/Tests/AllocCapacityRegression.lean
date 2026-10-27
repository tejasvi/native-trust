import NativeTrust
import LidoSRv3.Tests.AllocCapacityRegression
import F2_LidoSRv3_Tests_AllocCapacityRegression_0
import F2_LidoSRv3_Tests_AllocCapacityRegression_1
import F2_LidoSRv3_Tests_AllocCapacityRegression_2
import F2_LidoSRv3_Tests_AllocCapacityRegression_3
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth LidoSRv3.Tests.AllocCapacityRegression 0 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.AllocCapacityRegression 1 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.AllocCapacityRegression 2 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.AllocCapacityRegression 3 (config := { split := 8, trace := true })
