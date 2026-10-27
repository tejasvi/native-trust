import NativeTrust
import BO_S45_Parse
import BO_S45_L0
import BO_S45_L1
import BO_S45_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S45 BerryEsseen.Upper0423.Small.Data.Cover45.accepted
attribute [kernel_fact] BerryOpt.S45.final
#print axioms BerryOpt.S45.final
