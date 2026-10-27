import NativeTrust
import CpcMini.Proofs.TypePreservation.Common
import F2_CpcMini_Proofs_TypePreservation_Common_0
import F2_CpcMini_Proofs_TypePreservation_Common_1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth CpcMini.Proofs.TypePreservation.Common 0 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.TypePreservation.Common 1 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.TypePreservation.Common 2 (config := { split := 8, trace := true })
