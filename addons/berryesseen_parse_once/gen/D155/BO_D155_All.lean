import NativeTrust
import BO_D155_Parse
import BO_D155_L0
import BO_D155_L1
import BO_D155_L2
import BO_D155_L3
import BO_D155_L4
import BO_D155_L5
import BO_D155_L6
import BO_D155_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D155 BerryEsseen.Upper0423.Covers.Data.DW155.accepted
attribute [kernel_fact] BerryOpt.D155.final
#print axioms BerryOpt.D155.final
