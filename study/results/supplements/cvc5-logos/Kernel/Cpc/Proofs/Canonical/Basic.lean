import NativeTrust
import Cpc.Proofs.Canonical.Basic
import F2_Cpc_Proofs_Canonical_Basic_0
import F2_Cpc_Proofs_Canonical_Basic_1
import F2_Cpc_Proofs_Canonical_Basic_2
import F2_Cpc_Proofs_Canonical_Basic_3
import F2_Cpc_Proofs_Canonical_Basic_4
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.Canonical.Basic 0 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Canonical.Basic 1 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Canonical.Basic 2 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Canonical.Basic 3 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Canonical.Basic 4 (config := { split := 8, trace := true })
