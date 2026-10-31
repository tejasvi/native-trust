import NativeTrust
import BO_D244_Parse
import BO_D244_L0
import BO_D244_L1
import BO_D244_L2
import BO_D244_L3
import BO_D244_L4
import BO_D244_L5
import BO_D244_L6
import BO_D244_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D244 BerryEsseen.Upper0423.Covers.Data.DW244.accepted
attribute [kernel_fact] BerryOpt.D244.final
#print axioms BerryOpt.D244.final
