import NativeTrust
import BO_S36_Parse
import BO_S36_L0
import BO_S36_L1
import BO_S36_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S36 BerryEsseen.Upper0423.Small.Data.Cover36.accepted
attribute [kernel_fact] BerryOpt.S36.final
#print axioms BerryOpt.S36.final
