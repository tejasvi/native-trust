import NativeTrust
import BO_D165_Parse
import BO_D165_L0
import BO_D165_L1
import BO_D165_L2
import BO_D165_L3
import BO_D165_L4
import BO_D165_L5
import BO_D165_L6
import BO_D165_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D165 BerryEsseen.Upper0423.Covers.Data.DW165.accepted
attribute [kernel_fact] BerryOpt.D165.final
#print axioms BerryOpt.D165.final
