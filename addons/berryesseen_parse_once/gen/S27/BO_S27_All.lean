import NativeTrust
import BO_S27_Parse
import BO_S27_L0
import BO_S27_L1
import BO_S27_L2
import BO_S27_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S27 BerryEsseen.Upper0423.Small.Data.Cover27.accepted
attribute [kernel_fact] BerryOpt.S27.final
#print axioms BerryOpt.S27.final
