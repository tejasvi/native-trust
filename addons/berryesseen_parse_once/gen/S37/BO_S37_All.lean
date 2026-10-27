import NativeTrust
import BO_S37_Parse
import BO_S37_L0
import BO_S37_L1
import BO_S37_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S37 BerryEsseen.Upper0423.Small.Data.Cover37.accepted
attribute [kernel_fact] BerryOpt.S37.final
#print axioms BerryOpt.S37.final
