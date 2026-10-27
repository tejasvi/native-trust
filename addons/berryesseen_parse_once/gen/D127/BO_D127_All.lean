import NativeTrust
import BO_D127_Parse
import BO_D127_L0
import BO_D127_L1
import BO_D127_L2
import BO_D127_L3
import BO_D127_L4
import BO_D127_L5
import BO_D127_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D127 BerryEsseen.Upper0423.Covers.Data.DW127.accepted
attribute [kernel_fact] BerryOpt.D127.final
#print axioms BerryOpt.D127.final
