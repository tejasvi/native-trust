import NativeTrust
import BO_D192_Parse
import BO_D192_L0
import BO_D192_L1
import BO_D192_L2
import BO_D192_L3
import BO_D192_L4
import BO_D192_L5
import BO_D192_L6
import BO_D192_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D192 BerryEsseen.Upper0423.Covers.Data.DW192.accepted
attribute [kernel_fact] BerryOpt.D192.final
#print axioms BerryOpt.D192.final
