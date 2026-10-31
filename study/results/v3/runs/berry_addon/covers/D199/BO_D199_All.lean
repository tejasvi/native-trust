import NativeTrust
import BO_D199_Parse
import BO_D199_L0
import BO_D199_L1
import BO_D199_L2
import BO_D199_L3
import BO_D199_L4
import BO_D199_L5
import BO_D199_L6
import BO_D199_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D199 BerryEsseen.Upper0423.Covers.Data.DW199.accepted
attribute [kernel_fact] BerryOpt.D199.final
#print axioms BerryOpt.D199.final
