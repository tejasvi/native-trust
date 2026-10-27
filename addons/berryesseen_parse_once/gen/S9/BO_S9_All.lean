import NativeTrust
import BO_S9_Parse
import BO_S9_L0
import BO_S9_L1
import BO_S9_L2
import BO_S9_L3
import BO_S9_L4
import BO_S9_L5
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S9 BerryEsseen.Upper0423.Small.Data.Cover9.accepted
attribute [kernel_fact] BerryOpt.S9.final
#print axioms BerryOpt.S9.final
