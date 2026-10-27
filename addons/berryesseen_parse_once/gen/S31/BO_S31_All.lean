import NativeTrust
import BO_S31_Parse
import BO_S31_L0
import BO_S31_L1
import BO_S31_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S31 BerryEsseen.Upper0423.Small.Data.Cover31.accepted
attribute [kernel_fact] BerryOpt.S31.final
#print axioms BerryOpt.S31.final
