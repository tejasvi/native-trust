import NativeTrust
import BO_S13_Parse
import BO_S13_L0
import BO_S13_L1
import BO_S13_L2
import BO_S13_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S13 BerryEsseen.Upper0423.Small.Data.Cover13.accepted
attribute [kernel_fact] BerryOpt.S13.final
#print axioms BerryOpt.S13.final
