import NativeTrust
import BO_D242_Parse
import BO_D242_L0
import BO_D242_L1
import BO_D242_L2
import BO_D242_L3
import BO_D242_L4
import BO_D242_L5
import BO_D242_L6
import BO_D242_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D242 BerryEsseen.Upper0423.Covers.Data.DW242.accepted
attribute [kernel_fact] BerryOpt.D242.final
#print axioms BerryOpt.D242.final
