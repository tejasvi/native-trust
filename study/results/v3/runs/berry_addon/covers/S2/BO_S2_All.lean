import NativeTrust
import BO_S2_Parse
import BO_S2_L0
import BO_S2_L1
import BO_S2_L2
import BO_S2_L3
import BO_S2_L4
import BO_S2_L5
import BO_S2_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S2 BerryEsseen.Upper0423.Small.Data.Cover2.accepted
attribute [kernel_fact] BerryOpt.S2.final
#print axioms BerryOpt.S2.final
