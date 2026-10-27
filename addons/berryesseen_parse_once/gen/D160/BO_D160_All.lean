import NativeTrust
import BO_D160_Parse
import BO_D160_L0
import BO_D160_L1
import BO_D160_L2
import BO_D160_L3
import BO_D160_L4
import BO_D160_L5
import BO_D160_L6
import BO_D160_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D160 BerryEsseen.Upper0423.Covers.Data.DW160.accepted
attribute [kernel_fact] BerryOpt.D160.final
#print axioms BerryOpt.D160.final
