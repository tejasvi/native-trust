import NativeTrust
import BO_S57_Parse
import BO_S57_L0
import BO_S57_L1
import BO_S57_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S57 BerryEsseen.Upper0423.Small.Data.Cover57.accepted
attribute [kernel_fact] BerryOpt.S57.final
#print axioms BerryOpt.S57.final
