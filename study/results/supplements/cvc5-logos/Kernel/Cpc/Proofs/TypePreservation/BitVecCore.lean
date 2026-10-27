import NativeTrust
import Cpc.Proofs.TypePreservation.BitVecCore
import F2_Cpc_Proofs_TypePreservation_BitVecCore_0
import F2_Cpc_Proofs_TypePreservation_BitVecCore_1
import F2_Cpc_Proofs_TypePreservation_BitVecCore_2
import F2_Cpc_Proofs_TypePreservation_BitVecCore_3
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.TypePreservation.BitVecCore 0 (config := { split := 8, trace := true })
