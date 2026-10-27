import NativeTrust
import BO_S33_Parse
import BO_S33_L0
import BO_S33_L1
import BO_S33_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S33 BerryEsseen.Upper0423.Small.Data.Cover33.accepted
attribute [kernel_fact] BerryOpt.S33.final
#print axioms BerryOpt.S33.final
