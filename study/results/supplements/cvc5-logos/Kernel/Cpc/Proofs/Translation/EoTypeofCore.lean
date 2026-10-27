import NativeTrust
import Cpc.Proofs.Translation.EoTypeofCore
import F2_Cpc_Proofs_Translation_Inversions_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.Translation.EoTypeofCore 0 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Translation.EoTypeofCore 1 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Translation.EoTypeofCore 2 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Translation.EoTypeofCore 3 (config := { split := 8, trace := true })
