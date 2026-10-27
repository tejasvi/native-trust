import NativeTrust
import BO_D109_Parse
import BO_D109_L0
import BO_D109_L1
import BO_D109_L2
import BO_D109_L3
import BO_D109_L4
import BO_D109_L5
import BO_D109_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D109 BerryEsseen.Upper0423.Covers.Data.DW109.accepted
attribute [kernel_fact] BerryOpt.D109.final
#print axioms BerryOpt.D109.final
