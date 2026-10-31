import NativeTrust
import BO_S23_Parse
import BO_S23_L0
import BO_S23_L1
import BO_S23_L2
import BO_S23_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S23 BerryEsseen.Upper0423.Small.Data.Cover23.accepted
attribute [kernel_fact] BerryOpt.S23.final
#print axioms BerryOpt.S23.final
