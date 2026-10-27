import NativeTrust
import BO_S62_Parse
import BO_S62_L0
import BO_S62_L1
import BO_S62_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S62 BerryEsseen.Upper0423.Small.Data.Cover62.accepted
attribute [kernel_fact] BerryOpt.S62.final
#print axioms BerryOpt.S62.final
