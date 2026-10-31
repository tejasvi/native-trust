import NativeTrust
import BO_S22_Parse
import BO_S22_L0
import BO_S22_L1
import BO_S22_L2
import BO_S22_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S22 BerryEsseen.Upper0423.Small.Data.Cover22.accepted
attribute [kernel_fact] BerryOpt.S22.final
#print axioms BerryOpt.S22.final
