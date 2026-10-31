import NativeTrust
import BO_D179_Parse
import BO_D179_L0
import BO_D179_L1
import BO_D179_L2
import BO_D179_L3
import BO_D179_L4
import BO_D179_L5
import BO_D179_L6
import BO_D179_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D179 BerryEsseen.Upper0423.Covers.Data.DW179.accepted
attribute [kernel_fact] BerryOpt.D179.final
#print axioms BerryOpt.D179.final
