import NativeTrust
import BO_S10_Parse
import BO_S10_L0
import BO_S10_L1
import BO_S10_L2
import BO_S10_L3
import BO_S10_L4
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S10 BerryEsseen.Upper0423.Small.Data.Cover10.accepted
attribute [kernel_fact] BerryOpt.S10.final
#print axioms BerryOpt.S10.final
