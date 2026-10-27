import NativeTrust
import BO_S41_Parse
import BO_S41_L0
import BO_S41_L1
import BO_S41_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S41 BerryEsseen.Upper0423.Small.Data.Cover41.accepted
attribute [kernel_fact] BerryOpt.S41.final
#print axioms BerryOpt.S41.final
