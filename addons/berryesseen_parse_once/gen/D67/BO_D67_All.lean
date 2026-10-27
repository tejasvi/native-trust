import NativeTrust
import BO_D67_Parse
import BO_D67_L0
import BO_D67_L1
import BO_D67_L2
import BO_D67_L3
import BO_D67_L4
import BO_D67_L5
import BO_D67_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D67 BerryEsseen.Upper0423.Covers.Data.DW67.accepted
attribute [kernel_fact] BerryOpt.D67.final
#print axioms BerryOpt.D67.final
