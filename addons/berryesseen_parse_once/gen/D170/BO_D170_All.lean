import NativeTrust
import BO_D170_Parse
import BO_D170_L0
import BO_D170_L1
import BO_D170_L2
import BO_D170_L3
import BO_D170_L4
import BO_D170_L5
import BO_D170_L6
import BO_D170_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D170 BerryEsseen.Upper0423.Covers.Data.DW170.accepted
attribute [kernel_fact] BerryOpt.D170.final
#print axioms BerryOpt.D170.final
