import NativeTrust
import BO_S47_Parse
import BO_S47_L0
import BO_S47_L1
import BO_S47_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S47 BerryEsseen.Upper0423.Small.Data.Cover47.accepted
attribute [kernel_fact] BerryOpt.S47.final
#print axioms BerryOpt.S47.final
