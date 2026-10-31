import NativeTrust
import BO_D163_Parse
import BO_D163_L0
import BO_D163_L1
import BO_D163_L2
import BO_D163_L3
import BO_D163_L4
import BO_D163_L5
import BO_D163_L6
import BO_D163_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D163 BerryEsseen.Upper0423.Covers.Data.DW163.accepted
attribute [kernel_fact] BerryOpt.D163.final
#print axioms BerryOpt.D163.final
