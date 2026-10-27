import NativeTrust
import BO_S29_Parse
import BO_S29_L0
import BO_S29_L1
import BO_S29_L2
import BO_S29_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S29 BerryEsseen.Upper0423.Small.Data.Cover29.accepted
attribute [kernel_fact] BerryOpt.S29.final
#print axioms BerryOpt.S29.final
