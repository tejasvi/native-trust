import NativeTrust
import Cpc.Proofs.Rules.Re_star_emp
import F2_Cpc_Proofs_RuleSupport_Contract_0
import F2_Cpc_Proofs_Rules_Re_star_emp_0
import F2_Cpc_Proofs_Rules_Re_star_emp_1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.Rules.Re_star_emp 0 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Rules.Re_star_emp 1 (config := { split := 8, trace := true })
