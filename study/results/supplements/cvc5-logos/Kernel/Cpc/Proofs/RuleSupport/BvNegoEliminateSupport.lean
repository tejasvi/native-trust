import NativeTrust
import Cpc.Proofs.RuleSupport.BvNegoEliminateSupport
import F2_Cpc_Proofs_RuleSupport_BvNegoEliminateSupport_0
import F2_Cpc_Proofs_RuleSupport_BvNegoEliminateSupport_1
import F2_Cpc_Proofs_RuleSupport_BvNegoEliminateSupport_2
import F2_Cpc_Proofs_RuleSupport_BvNegoEliminateSupport_3
import F2_Cpc_Proofs_RuleSupport_BvNegoEliminateSupport_4
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.RuleSupport.BvNegoEliminateSupport 0 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.RuleSupport.BvNegoEliminateSupport 1 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.RuleSupport.BvNegoEliminateSupport 2 (config := { split := 8, trace := true })
