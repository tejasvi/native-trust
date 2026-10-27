import NativeTrust
import BO_S28_Parse
import BO_S28_L0
import BO_S28_L1
import BO_S28_L2
import BO_S28_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S28 BerryEsseen.Upper0423.Small.Data.Cover28.accepted
attribute [kernel_fact] BerryOpt.S28.final
#print axioms BerryOpt.S28.final
