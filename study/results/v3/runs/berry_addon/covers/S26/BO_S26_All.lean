import NativeTrust
import BO_S26_Parse
import BO_S26_L0
import BO_S26_L1
import BO_S26_L2
import BO_S26_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S26 BerryEsseen.Upper0423.Small.Data.Cover26.accepted
attribute [kernel_fact] BerryOpt.S26.final
#print axioms BerryOpt.S26.final
