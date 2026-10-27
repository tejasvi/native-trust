import NativeTrust
import Cpc.Proofs.RuleSupport.SkolemizeSupport
import F2_Cpc_Proofs_RuleSupport_SkolemizeSupport_0
import F2_Cpc_Proofs_RuleSupport_SkolemizeSupport_1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.RuleSupport.SkolemizeSupport 0 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.RuleSupport.SkolemizeSupport 1 (config := { split := 8, trace := true })
