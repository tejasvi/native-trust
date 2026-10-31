import NativeTrust
import BO_S39_Parse
import BO_S39_L0
import BO_S39_L1
import BO_S39_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S39 BerryEsseen.Upper0423.Small.Data.Cover39.accepted
attribute [kernel_fact] BerryOpt.S39.final
#print axioms BerryOpt.S39.final
