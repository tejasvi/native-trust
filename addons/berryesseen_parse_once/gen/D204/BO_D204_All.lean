import NativeTrust
import BO_D204_Parse
import BO_D204_L0
import BO_D204_L1
import BO_D204_L2
import BO_D204_L3
import BO_D204_L4
import BO_D204_L5
import BO_D204_L6
import BO_D204_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D204 BerryEsseen.Upper0423.Covers.Data.DW204.accepted
attribute [kernel_fact] BerryOpt.D204.final
#print axioms BerryOpt.D204.final
