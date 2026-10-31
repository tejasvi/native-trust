import NativeTrust
import BO_S12_Parse
import BO_S12_L0
import BO_S12_L1
import BO_S12_L2
import BO_S12_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S12 BerryEsseen.Upper0423.Small.Data.Cover12.accepted
attribute [kernel_fact] BerryOpt.S12.final
#print axioms BerryOpt.S12.final
