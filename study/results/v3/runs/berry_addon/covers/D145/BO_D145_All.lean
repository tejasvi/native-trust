import NativeTrust
import BO_D145_Parse
import BO_D145_L0
import BO_D145_L1
import BO_D145_L2
import BO_D145_L3
import BO_D145_L4
import BO_D145_L5
import BO_D145_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D145 BerryEsseen.Upper0423.Covers.Data.DW145.accepted
attribute [kernel_fact] BerryOpt.D145.final
#print axioms BerryOpt.D145.final
