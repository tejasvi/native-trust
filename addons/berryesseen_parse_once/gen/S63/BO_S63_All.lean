import NativeTrust
import BO_S63_Parse
import BO_S63_L0
import BO_S63_L1
import BO_S63_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S63 BerryEsseen.Upper0423.Small.Data.Cover63.accepted
attribute [kernel_fact] BerryOpt.S63.final
#print axioms BerryOpt.S63.final
