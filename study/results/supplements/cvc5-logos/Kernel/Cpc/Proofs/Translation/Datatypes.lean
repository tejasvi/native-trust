import NativeTrust
import Cpc.Proofs.Translation.Datatypes
import F2_Cpc_Proofs_Translation_Datatypes_0
import F2_Cpc_Proofs_Translation_Datatypes_1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.Translation.Datatypes 0 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Translation.Datatypes 1 (config := { split := 8, trace := true })
