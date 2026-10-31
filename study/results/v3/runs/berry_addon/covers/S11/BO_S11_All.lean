import NativeTrust
import BO_S11_Parse
import BO_S11_L0
import BO_S11_L1
import BO_S11_L2
import BO_S11_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S11 BerryEsseen.Upper0423.Small.Data.Cover11.accepted
attribute [kernel_fact] BerryOpt.S11.final
#print axioms BerryOpt.S11.final
