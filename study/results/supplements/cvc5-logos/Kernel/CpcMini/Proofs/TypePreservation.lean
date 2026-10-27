import NativeTrust
import CpcMini.Proofs.TypePreservation
import F2_CpcMini_Proofs_TypePreservation_0
import F2_CpcMini_Proofs_TypePreservation_Common_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth CpcMini.Proofs.TypePreservation 0 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.TypePreservation 1 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.TypePreservation 2 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.TypePreservation 3 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.TypePreservation 4 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.TypePreservation 5 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.TypePreservation 6 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.TypePreservation 7 (config := { split := 8, trace := true })
