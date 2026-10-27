import NativeTrust
import LidoSRv3.Audit.Verity.Tests.ConsolidationFee
import F2_LidoSRv3_Audit_Verity_Tests_ConsolidationFee_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth LidoSRv3.Audit.Verity.Tests.ConsolidationFee 0 (config := { split := 8, trace := true })
