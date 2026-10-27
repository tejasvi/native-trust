import NativeTrust
import CpcMini.Proofs.RuleSupport.Contract
import F2_CpcMini_Proofs_RuleSupport_Contract_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth CpcMini.Proofs.RuleSupport.Contract 0 (config := { split := 8, trace := true })
