import NativeTrust
import BO_D106_Parse
import BO_D106_L0
import BO_D106_L1
import BO_D106_L2
import BO_D106_L3
import BO_D106_L4
import BO_D106_L5
import BO_D106_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D106 BerryEsseen.Upper0423.Covers.Data.DW106.accepted
attribute [kernel_fact] BerryOpt.D106.final
#print axioms BerryOpt.D106.final
