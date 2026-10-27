import NativeTrust
import BO_D136_Parse
import BO_D136_L0
import BO_D136_L1
import BO_D136_L2
import BO_D136_L3
import BO_D136_L4
import BO_D136_L5
import BO_D136_L6
import BO_D136_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D136 BerryEsseen.Upper0423.Covers.Data.DW136.accepted
attribute [kernel_fact] BerryOpt.D136.final
#print axioms BerryOpt.D136.final
