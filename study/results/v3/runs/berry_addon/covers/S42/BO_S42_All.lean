import NativeTrust
import BO_S42_Parse
import BO_S42_L0
import BO_S42_L1
import BO_S42_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S42 BerryEsseen.Upper0423.Small.Data.Cover42.accepted
attribute [kernel_fact] BerryOpt.S42.final
#print axioms BerryOpt.S42.final
