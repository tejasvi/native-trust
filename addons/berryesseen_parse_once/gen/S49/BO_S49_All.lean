import NativeTrust
import BO_S49_Parse
import BO_S49_L0
import BO_S49_L1
import BO_S49_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S49 BerryEsseen.Upper0423.Small.Data.Cover49.accepted
attribute [kernel_fact] BerryOpt.S49.final
#print axioms BerryOpt.S49.final
