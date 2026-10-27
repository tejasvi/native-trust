import NativeTrust
import BO_S20_Parse
import BO_S20_L0
import BO_S20_L1
import BO_S20_L2
import BO_S20_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S20 BerryEsseen.Upper0423.Small.Data.Cover20.accepted
attribute [kernel_fact] BerryOpt.S20.final
#print axioms BerryOpt.S20.final
