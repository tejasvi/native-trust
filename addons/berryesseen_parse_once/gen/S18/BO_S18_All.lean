import NativeTrust
import BO_S18_Parse
import BO_S18_L0
import BO_S18_L1
import BO_S18_L2
import BO_S18_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S18 BerryEsseen.Upper0423.Small.Data.Cover18.accepted
attribute [kernel_fact] BerryOpt.S18.final
#print axioms BerryOpt.S18.final
