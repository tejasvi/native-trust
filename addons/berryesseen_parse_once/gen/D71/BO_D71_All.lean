import NativeTrust
import BO_D71_Parse
import BO_D71_L0
import BO_D71_L1
import BO_D71_L2
import BO_D71_L3
import BO_D71_L4
import BO_D71_L5
import BO_D71_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D71 BerryEsseen.Upper0423.Covers.Data.DW71.accepted
attribute [kernel_fact] BerryOpt.D71.final
#print axioms BerryOpt.D71.final
