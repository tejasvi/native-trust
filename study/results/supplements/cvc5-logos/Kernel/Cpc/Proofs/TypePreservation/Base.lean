import NativeTrust
import Cpc.Proofs.TypePreservation.Base
import F2_Cpc_Proofs_TypePreservation_Base_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.TypePreservation.Base 0 (config := { split := 8, trace := true })
