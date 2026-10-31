import NativeTrust
import BO_S15_Parse
import BO_S15_L0
import BO_S15_L1
import BO_S15_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S15 BerryEsseen.Upper0423.Small.Data.Cover15.accepted
attribute [kernel_fact] BerryOpt.S15.final
#print axioms BerryOpt.S15.final
