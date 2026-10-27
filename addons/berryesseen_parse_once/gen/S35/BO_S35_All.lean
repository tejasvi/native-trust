import NativeTrust
import BO_S35_Parse
import BO_S35_L0
import BO_S35_L1
import BO_S35_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S35 BerryEsseen.Upper0423.Small.Data.Cover35.accepted
attribute [kernel_fact] BerryOpt.S35.final
#print axioms BerryOpt.S35.final
