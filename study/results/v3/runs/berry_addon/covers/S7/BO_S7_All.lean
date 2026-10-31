import NativeTrust
import BO_S7_Parse
import BO_S7_L0
import BO_S7_L1
import BO_S7_L2
import BO_S7_L3
import BO_S7_L4
import BO_S7_L5
import BO_S7_L6
import BO_S7_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S7 BerryEsseen.Upper0423.Small.Data.Cover7.accepted
attribute [kernel_fact] BerryOpt.S7.final
#print axioms BerryOpt.S7.final
