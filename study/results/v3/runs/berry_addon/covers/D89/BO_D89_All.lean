import NativeTrust
import BO_D89_Parse
import BO_D89_L0
import BO_D89_L1
import BO_D89_L2
import BO_D89_L3
import BO_D89_L4
import BO_D89_L5
import BO_D89_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D89 BerryEsseen.Upper0423.Covers.Data.DW89.accepted
attribute [kernel_fact] BerryOpt.D89.final
#print axioms BerryOpt.D89.final
