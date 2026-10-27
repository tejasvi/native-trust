import NativeTrust
import BO_S60_Parse
import BO_S60_L0
import BO_S60_L1
import BO_S60_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S60 BerryEsseen.Upper0423.Small.Data.Cover60.accepted
attribute [kernel_fact] BerryOpt.S60.final
#print axioms BerryOpt.S60.final
