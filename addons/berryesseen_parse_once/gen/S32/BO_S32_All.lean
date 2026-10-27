import NativeTrust
import BO_S32_Parse
import BO_S32_L0
import BO_S32_L1
import BO_S32_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S32 BerryEsseen.Upper0423.Small.Data.Cover32.accepted
attribute [kernel_fact] BerryOpt.S32.final
#print axioms BerryOpt.S32.final
