import NativeTrust
import BO_S54_Parse
import BO_S54_L0
import BO_S54_L1
import BO_S54_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S54 BerryEsseen.Upper0423.Small.Data.Cover54.accepted
attribute [kernel_fact] BerryOpt.S54.final
#print axioms BerryOpt.S54.final
