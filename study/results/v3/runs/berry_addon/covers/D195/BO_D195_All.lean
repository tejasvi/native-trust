import NativeTrust
import BO_D195_Parse
import BO_D195_L0
import BO_D195_L1
import BO_D195_L2
import BO_D195_L3
import BO_D195_L4
import BO_D195_L5
import BO_D195_L6
import BO_D195_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D195 BerryEsseen.Upper0423.Covers.Data.DW195.accepted
attribute [kernel_fact] BerryOpt.D195.final
#print axioms BerryOpt.D195.final
