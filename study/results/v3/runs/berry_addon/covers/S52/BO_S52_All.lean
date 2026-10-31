import NativeTrust
import BO_S52_Parse
import BO_S52_L0
import BO_S52_L1
import BO_S52_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S52 BerryEsseen.Upper0423.Small.Data.Cover52.accepted
attribute [kernel_fact] BerryOpt.S52.final
#print axioms BerryOpt.S52.final
