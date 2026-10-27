import NativeTrust
import BO_S40_Parse
import BO_S40_L0
import BO_S40_L1
import BO_S40_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S40 BerryEsseen.Upper0423.Small.Data.Cover40.accepted
attribute [kernel_fact] BerryOpt.S40.final
#print axioms BerryOpt.S40.final
