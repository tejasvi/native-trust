import NativeTrust
import Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringFromInt
import F2_Cpc_Proofs_RuleSupport_Evaluate_Prelude_StringFromInt_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.RuleSupport.Evaluate.Prelude.StringFromInt 0 (config := { split := 8, trace := true })
