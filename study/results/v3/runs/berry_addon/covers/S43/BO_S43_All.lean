import NativeTrust
import BO_S43_Parse
import BO_S43_L0
import BO_S43_L1
import BO_S43_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S43 BerryEsseen.Upper0423.Small.Data.Cover43.accepted
attribute [kernel_fact] BerryOpt.S43.final
#print axioms BerryOpt.S43.final
