import NativeTrust
import BO_D115_Parse
import BO_D115_L0
import BO_D115_L1
import BO_D115_L2
import BO_D115_L3
import BO_D115_L4
import BO_D115_L5
import BO_D115_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D115 BerryEsseen.Upper0423.Covers.Data.DW115.accepted
attribute [kernel_fact] BerryOpt.D115.final
#print axioms BerryOpt.D115.final
