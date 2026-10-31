import NativeTrust
import BO_S8_Parse
import BO_S8_L0
import BO_S8_L1
import BO_S8_L2
import BO_S8_L3
import BO_S8_L4
import BO_S8_L5
import BO_S8_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S8 BerryEsseen.Upper0423.Small.Data.Cover8.accepted
attribute [kernel_fact] BerryOpt.S8.final
#print axioms BerryOpt.S8.final
