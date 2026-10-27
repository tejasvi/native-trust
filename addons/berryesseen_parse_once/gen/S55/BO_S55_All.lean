import NativeTrust
import BO_S55_Parse
import BO_S55_L0
import BO_S55_L1
import BO_S55_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S55 BerryEsseen.Upper0423.Small.Data.Cover55.accepted
attribute [kernel_fact] BerryOpt.S55.final
#print axioms BerryOpt.S55.final
