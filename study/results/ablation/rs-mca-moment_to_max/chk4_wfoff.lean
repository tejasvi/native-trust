import NativeTrust
import MomentToMax.PTEClusterPacking
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
#kernel_blockers_nth MomentToMax.PTEClusterPacking 1
trust_check_nth MomentToMax.PTEClusterPacking 1 (config := { split := 8, wf := false, trace := true })
