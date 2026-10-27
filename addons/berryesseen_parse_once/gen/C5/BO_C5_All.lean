import NativeTrust
import BO_C5_Parse
import BO_C5_L0
import BO_C5_L1
import BO_C5_L2
import BO_C5_L3
import BO_C5_L4
import BO_C5_L5
import BO_C5_L6
import BO_C5_L7
import BO_C5_L8
import BO_C5_L9
import BO_C5_L10
import BO_C5_L11
import BO_C5_L12
import BO_C5_L13
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.C5 BerryEsseen.Upper0423.Small.Data.Cover5.accepted
attribute [kernel_fact] BerryOpt.C5.final
#print axioms BerryOpt.C5.final
