import NativeTrust
import BO_D95_Parse
import BO_D95_L0
import BO_D95_L1
import BO_D95_L2
import BO_D95_L3
import BO_D95_L4
import BO_D95_L5
import BO_D95_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D95 BerryEsseen.Upper0423.Covers.Data.DW95.accepted
attribute [kernel_fact] BerryOpt.D95.final
#print axioms BerryOpt.D95.final
