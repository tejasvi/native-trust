import NativeTrust
import BO_S51_Parse
import BO_S51_L0
import BO_S51_L1
import BO_S51_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S51 BerryEsseen.Upper0423.Small.Data.Cover51.accepted
attribute [kernel_fact] BerryOpt.S51.final
#print axioms BerryOpt.S51.final
