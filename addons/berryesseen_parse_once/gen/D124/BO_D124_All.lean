import NativeTrust
import BO_D124_Parse
import BO_D124_L0
import BO_D124_L1
import BO_D124_L2
import BO_D124_L3
import BO_D124_L4
import BO_D124_L5
import BO_D124_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D124 BerryEsseen.Upper0423.Covers.Data.DW124.accepted
attribute [kernel_fact] BerryOpt.D124.final
#print axioms BerryOpt.D124.final
