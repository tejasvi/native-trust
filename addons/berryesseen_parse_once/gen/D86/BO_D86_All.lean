import NativeTrust
import BO_D86_Parse
import BO_D86_L0
import BO_D86_L1
import BO_D86_L2
import BO_D86_L3
import BO_D86_L4
import BO_D86_L5
import BO_D86_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D86 BerryEsseen.Upper0423.Covers.Data.DW86.accepted
attribute [kernel_fact] BerryOpt.D86.final
#print axioms BerryOpt.D86.final
