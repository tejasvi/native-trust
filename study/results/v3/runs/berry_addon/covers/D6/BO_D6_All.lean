import NativeTrust
import BO_D6_Parse
import BO_D6_L0
import BO_D6_L1
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D6 BerryEsseen.Upper0423.Covers.Data.DW6.accepted
attribute [kernel_fact] BerryOpt.D6.final
#print axioms BerryOpt.D6.final
