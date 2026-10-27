import NativeTrust
import BO_D225_Parse
import BO_D225_L0
import BO_D225_L1
import BO_D225_L2
import BO_D225_L3
import BO_D225_L4
import BO_D225_L5
import BO_D225_L6
import BO_D225_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D225 BerryEsseen.Upper0423.Covers.Data.DW225.accepted
attribute [kernel_fact] BerryOpt.D225.final
#print axioms BerryOpt.D225.final
