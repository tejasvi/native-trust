import NativeTrust
import BO_D231_Parse
import BO_D231_L0
import BO_D231_L1
import BO_D231_L2
import BO_D231_L3
import BO_D231_L4
import BO_D231_L5
import BO_D231_L6
import BO_D231_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D231 BerryEsseen.Upper0423.Covers.Data.DW231.accepted
attribute [kernel_fact] BerryOpt.D231.final
#print axioms BerryOpt.D231.final
