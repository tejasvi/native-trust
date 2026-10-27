import NativeTrust
import BO_D120_Parse
import BO_D120_L0
import BO_D120_L1
import BO_D120_L2
import BO_D120_L3
import BO_D120_L4
import BO_D120_L5
import BO_D120_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D120 BerryEsseen.Upper0423.Covers.Data.DW120.accepted
attribute [kernel_fact] BerryOpt.D120.final
#print axioms BerryOpt.D120.final
