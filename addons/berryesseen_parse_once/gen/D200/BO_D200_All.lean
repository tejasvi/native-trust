import NativeTrust
import BO_D200_Parse
import BO_D200_L0
import BO_D200_L1
import BO_D200_L2
import BO_D200_L3
import BO_D200_L4
import BO_D200_L5
import BO_D200_L6
import BO_D200_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D200 BerryEsseen.Upper0423.Covers.Data.DW200.accepted
attribute [kernel_fact] BerryOpt.D200.final
#print axioms BerryOpt.D200.final
