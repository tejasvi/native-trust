import NativeTrust
import BO_D247_Parse
import BO_D247_L0
import BO_D247_L1
import BO_D247_L2
import BO_D247_L3
import BO_D247_L4
import BO_D247_L5
import BO_D247_L6
import BO_D247_L7
import BO_D247_L8
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D247 BerryEsseen.Upper0423.Covers.Data.DW247.accepted
attribute [kernel_fact] BerryOpt.D247.final
#print axioms BerryOpt.D247.final
