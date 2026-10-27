import NativeTrust
import BO_S58_Parse
import BO_S58_L0
import BO_S58_L1
import BO_S58_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S58 BerryEsseen.Upper0423.Small.Data.Cover58.accepted
attribute [kernel_fact] BerryOpt.S58.final
#print axioms BerryOpt.S58.final
