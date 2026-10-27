import NativeTrust
import BO_D156_Parse
import BO_D156_L0
import BO_D156_L1
import BO_D156_L2
import BO_D156_L3
import BO_D156_L4
import BO_D156_L5
import BO_D156_L6
import BO_D156_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D156 BerryEsseen.Upper0423.Covers.Data.DW156.accepted
attribute [kernel_fact] BerryOpt.D156.final
#print axioms BerryOpt.D156.final
