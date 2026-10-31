import NativeTrust
import BO_D129_Parse
import BO_D129_L0
import BO_D129_L1
import BO_D129_L2
import BO_D129_L3
import BO_D129_L4
import BO_D129_L5
import BO_D129_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D129 BerryEsseen.Upper0423.Covers.Data.DW129.accepted
attribute [kernel_fact] BerryOpt.D129.final
#print axioms BerryOpt.D129.final
