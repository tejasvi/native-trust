import NativeTrust
import LidoSRv3.Tests.MinFirstAmountTxMutants
import F2_LidoSRv3_Tests_MinFirstAmountTxMutants_0
import F2_LidoSRv3_Tests_MinFirstAmountTxMutants_1
import F2_LidoSRv3_Tests_MinFirstAmountTxMutants_2
import F2_LidoSRv3_Tests_MinFirstAmountTxMutants_3
import F2_LidoSRv3_Tests_MinFirstAmountTxMutants_4
import F2_LidoSRv3_Tests_MinFirstAmountTxMutants_5
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth LidoSRv3.Tests.MinFirstAmountTxMutants 0 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.MinFirstAmountTxMutants 1 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.MinFirstAmountTxMutants 2 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.MinFirstAmountTxMutants 3 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.MinFirstAmountTxMutants 4 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.MinFirstAmountTxMutants 5 (config := { split := 8, trace := true })
