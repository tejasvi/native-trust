import NativeTrust
import Cpc.Proofs.RuleSupport.RegexRewriteSupport
import F2_Cpc_Proofs_RuleSupport_RegexRewriteSupport_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.RuleSupport.RegexRewriteSupport 0 (config := { split := 8, trace := true })
