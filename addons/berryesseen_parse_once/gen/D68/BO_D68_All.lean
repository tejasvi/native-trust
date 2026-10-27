import NativeTrust
import BO_D68_Parse
import BO_D68_L0
import BO_D68_L1
import BO_D68_L2
import BO_D68_L3
import BO_D68_L4
import BO_D68_L5
import BO_D68_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D68 BerryEsseen.Upper0423.Covers.Data.DW68.accepted
attribute [kernel_fact] BerryOpt.D68.final
#print axioms BerryOpt.D68.final
