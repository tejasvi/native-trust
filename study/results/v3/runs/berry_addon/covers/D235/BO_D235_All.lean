import NativeTrust
import BO_D235_Parse
import BO_D235_L0
import BO_D235_L1
import BO_D235_L2
import BO_D235_L3
import BO_D235_L4
import BO_D235_L5
import BO_D235_L6
import BO_D235_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D235 BerryEsseen.Upper0423.Covers.Data.DW235.accepted
attribute [kernel_fact] BerryOpt.D235.final
#print axioms BerryOpt.D235.final
