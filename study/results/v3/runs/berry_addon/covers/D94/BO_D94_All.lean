import NativeTrust
import BO_D94_Parse
import BO_D94_L0
import BO_D94_L1
import BO_D94_L2
import BO_D94_L3
import BO_D94_L4
import BO_D94_L5
import BO_D94_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D94 BerryEsseen.Upper0423.Covers.Data.DW94.accepted
attribute [kernel_fact] BerryOpt.D94.final
#print axioms BerryOpt.D94.final
