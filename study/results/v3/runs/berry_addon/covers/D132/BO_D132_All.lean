import NativeTrust
import BO_D132_Parse
import BO_D132_L0
import BO_D132_L1
import BO_D132_L2
import BO_D132_L3
import BO_D132_L4
import BO_D132_L5
import BO_D132_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D132 BerryEsseen.Upper0423.Covers.Data.DW132.accepted
attribute [kernel_fact] BerryOpt.D132.final
#print axioms BerryOpt.D132.final
