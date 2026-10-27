import NativeTrust
import Cpc.Proofs.Canonical.Fresh
import F2_Cpc_Proofs_Canonical_Fresh_0
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
trust_check_nth Cpc.Proofs.Canonical.Fresh 0 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Canonical.Fresh 1 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Canonical.Fresh 2 (config := { split := 8, trace := true })
trust_check_nth Cpc.Proofs.Canonical.Fresh 3 (config := { split := 8, trace := true })
