import NativeTrust
import Cpc.Proofs.Rules.Re_star_union_drop_emp
import F2_Cpc_Proofs_Canonical_Basic_0
import F2_Cpc_Proofs_Canonical_Basic_2
import F2_Cpc_Proofs_Canonical_Basic_4
import F2_Cpc_Proofs_RuleSupport_Contract_0
import F2_Cpc_Proofs_Rules_Re_star_union_drop_emp_0
import F2_Cpc_Proofs_TypePreservation_Base_0
import F2_Cpc_Proofs_TypePreservation_BitVecCore_0
import F2_Cpc_Proofs_TypePreservation_BitVecCore_1
import F2_Cpc_Proofs_TypePreservation_BitVecCore_2
import F2_Cpc_Proofs_TypePreservation_BitVecCore_3
import F2_Cpc_Proofs_TypePreservation_Common_0
import F2_Cpc_Proofs_TypePreservation_Common_1
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.Rules.Re_star_union_drop_emp 0 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Rules.Re_star_union_drop_emp 1 (config := { split := 8, trace := true })
