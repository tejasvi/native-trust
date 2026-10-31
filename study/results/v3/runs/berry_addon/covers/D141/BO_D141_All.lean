import NativeTrust
import BO_D141_Parse
import BO_D141_L0
import BO_D141_L1
import BO_D141_L2
import BO_D141_L3
import BO_D141_L4
import BO_D141_L5
import BO_D141_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D141 BerryEsseen.Upper0423.Covers.Data.DW141.accepted
attribute [kernel_fact] BerryOpt.D141.final
#print axioms BerryOpt.D141.final
