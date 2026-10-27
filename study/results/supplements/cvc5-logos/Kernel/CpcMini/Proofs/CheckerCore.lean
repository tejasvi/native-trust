import NativeTrust
import CpcMini.Proofs.CheckerCore
import F2_CpcMini_Proofs_CheckerCore_0
import F2_CpcMini_Proofs_CheckerCore_1
import F2_CpcMini_Proofs_CheckerState_0
import F2_CpcMini_Proofs_RuleSupport_Contract_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth CpcMini.Proofs.CheckerCore 0 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.CheckerCore 1 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.CheckerCore 2 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.CheckerCore 3 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.CheckerCore 4 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.CheckerCore 5 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.CheckerCore 6 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.CheckerCore 7 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.CheckerCore 8 (config := { split := 8, trace := true })
trust_check_nth CpcMini.Proofs.CheckerCore 9 (config := { split := 8, trace := true })
