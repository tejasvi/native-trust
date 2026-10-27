import NativeTrust
import BO_D125_Parse
import BO_D125_L0
import BO_D125_L1
import BO_D125_L2
import BO_D125_L3
import BO_D125_L4
import BO_D125_L5
import BO_D125_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D125 BerryEsseen.Upper0423.Covers.Data.DW125.accepted
attribute [kernel_fact] BerryOpt.D125.final
#print axioms BerryOpt.D125.final
