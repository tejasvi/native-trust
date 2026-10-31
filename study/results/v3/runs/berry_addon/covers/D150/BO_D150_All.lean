import NativeTrust
import BO_D150_Parse
import BO_D150_L0
import BO_D150_L1
import BO_D150_L2
import BO_D150_L3
import BO_D150_L4
import BO_D150_L5
import BO_D150_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D150 BerryEsseen.Upper0423.Covers.Data.DW150.accepted
attribute [kernel_fact] BerryOpt.D150.final
#print axioms BerryOpt.D150.final
