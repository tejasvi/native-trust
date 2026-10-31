import NativeTrust
import BO_S46_Parse
import BO_S46_L0
import BO_S46_L1
import BO_S46_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S46 BerryEsseen.Upper0423.Small.Data.Cover46.accepted
attribute [kernel_fact] BerryOpt.S46.final
#print axioms BerryOpt.S46.final
