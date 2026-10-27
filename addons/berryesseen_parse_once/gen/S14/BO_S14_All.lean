import NativeTrust
import BO_S14_Parse
import BO_S14_L0
import BO_S14_L1
import BO_S14_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S14 BerryEsseen.Upper0423.Small.Data.Cover14.accepted
attribute [kernel_fact] BerryOpt.S14.final
#print axioms BerryOpt.S14.final
