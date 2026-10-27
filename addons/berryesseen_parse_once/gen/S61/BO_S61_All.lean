import NativeTrust
import BO_S61_Parse
import BO_S61_L0
import BO_S61_L1
import BO_S61_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S61 BerryEsseen.Upper0423.Small.Data.Cover61.accepted
attribute [kernel_fact] BerryOpt.S61.final
#print axioms BerryOpt.S61.final
