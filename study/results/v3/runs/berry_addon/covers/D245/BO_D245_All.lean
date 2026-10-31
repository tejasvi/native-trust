import NativeTrust
import BO_D245_Parse
import BO_D245_L0
import BO_D245_L1
import BO_D245_L2
import BO_D245_L3
import BO_D245_L4
import BO_D245_L5
import BO_D245_L6
import BO_D245_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D245 BerryEsseen.Upper0423.Covers.Data.DW245.accepted
attribute [kernel_fact] BerryOpt.D245.final
#print axioms BerryOpt.D245.final
