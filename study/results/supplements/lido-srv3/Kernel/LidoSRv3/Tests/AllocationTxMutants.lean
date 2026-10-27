import NativeTrust
import LidoSRv3.Tests.AllocationTxMutants
import F2_LidoSRv3_Tests_AllocationTxMutants_0
import F2_LidoSRv3_Tests_AllocationTxMutants_1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth LidoSRv3.Tests.AllocationTxMutants 0 (config := { split := 8, trace := true })
trust_check_nth LidoSRv3.Tests.AllocationTxMutants 1 (config := { split := 8, trace := true })
