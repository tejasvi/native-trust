import NativeTrust
import BO_D180_Parse
import BO_D180_L0
import BO_D180_L1
import BO_D180_L2
import BO_D180_L3
import BO_D180_L4
import BO_D180_L5
import BO_D180_L6
import BO_D180_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D180 BerryEsseen.Upper0423.Covers.Data.DW180.accepted
attribute [kernel_fact] BerryOpt.D180.final
#print axioms BerryOpt.D180.final
