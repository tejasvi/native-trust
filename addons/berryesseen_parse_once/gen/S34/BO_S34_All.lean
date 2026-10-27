import NativeTrust
import BO_S34_Parse
import BO_S34_L0
import BO_S34_L1
import BO_S34_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S34 BerryEsseen.Upper0423.Small.Data.Cover34.accepted
attribute [kernel_fact] BerryOpt.S34.final
#print axioms BerryOpt.S34.final
