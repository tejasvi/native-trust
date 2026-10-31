import NativeTrust
import BO_C6_Parse
import BO_C6_L0
import BO_C6_L1
import BO_C6_L2
import BO_C6_L3
import BO_C6_L4
import BO_C6_L5
import BO_C6_L6
import BO_C6_L7
import BO_C6_L8
import BO_C6_L9
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.C6 BerryEsseen.Upper0423.Small.Data.Cover6.accepted
attribute [kernel_fact] BerryOpt.C6.final
#print axioms BerryOpt.C6.final
