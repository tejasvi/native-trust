import NativeTrust
import BO_S25_Parse
import BO_S25_L0
import BO_S25_L1
import BO_S25_L2
import BO_S25_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S25 BerryEsseen.Upper0423.Small.Data.Cover25.accepted
attribute [kernel_fact] BerryOpt.S25.final
#print axioms BerryOpt.S25.final
