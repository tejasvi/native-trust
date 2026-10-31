import NativeTrust
import BO_S56_Parse
import BO_S56_L0
import BO_S56_L1
import BO_S56_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S56 BerryEsseen.Upper0423.Small.Data.Cover56.accepted
attribute [kernel_fact] BerryOpt.S56.final
#print axioms BerryOpt.S56.final
