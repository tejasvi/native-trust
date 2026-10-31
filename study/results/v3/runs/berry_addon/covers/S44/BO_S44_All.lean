import NativeTrust
import BO_S44_Parse
import BO_S44_L0
import BO_S44_L1
import BO_S44_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S44 BerryEsseen.Upper0423.Small.Data.Cover44.accepted
attribute [kernel_fact] BerryOpt.S44.final
#print axioms BerryOpt.S44.final
