import NativeTrust
import BO_D111_Parse
import BO_D111_L0
import BO_D111_L1
import BO_D111_L2
import BO_D111_L3
import BO_D111_L4
import BO_D111_L5
import BO_D111_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D111 BerryEsseen.Upper0423.Covers.Data.DW111.accepted
attribute [kernel_fact] BerryOpt.D111.final
#print axioms BerryOpt.D111.final
