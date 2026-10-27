import NativeTrust
import BO_S19_Parse
import BO_S19_L0
import BO_S19_L1
import BO_S19_L2
import BO_S19_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S19 BerryEsseen.Upper0423.Small.Data.Cover19.accepted
attribute [kernel_fact] BerryOpt.S19.final
#print axioms BerryOpt.S19.final
