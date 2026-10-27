import NativeTrust
import BO_D98_Parse
import BO_D98_L0
import BO_D98_L1
import BO_D98_L2
import BO_D98_L3
import BO_D98_L4
import BO_D98_L5
import BO_D98_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D98 BerryEsseen.Upper0423.Covers.Data.DW98.accepted
attribute [kernel_fact] BerryOpt.D98.final
#print axioms BerryOpt.D98.final
