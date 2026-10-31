import NativeTrust
import BO_D72_Parse
import BO_D72_L0
import BO_D72_L1
import BO_D72_L2
import BO_D72_L3
import BO_D72_L4
import BO_D72_L5
import BO_D72_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D72 BerryEsseen.Upper0423.Covers.Data.DW72.accepted
attribute [kernel_fact] BerryOpt.D72.final
#print axioms BerryOpt.D72.final
