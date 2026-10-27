import NativeTrust
import BO_S16_Parse
import BO_S16_L0
import BO_S16_L1
import BO_S16_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S16 BerryEsseen.Upper0423.Small.Data.Cover16.accepted
attribute [kernel_fact] BerryOpt.S16.final
#print axioms BerryOpt.S16.final
