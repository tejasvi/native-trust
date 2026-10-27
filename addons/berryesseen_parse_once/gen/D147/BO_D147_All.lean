import NativeTrust
import BO_D147_Parse
import BO_D147_L0
import BO_D147_L1
import BO_D147_L2
import BO_D147_L3
import BO_D147_L4
import BO_D147_L5
import BO_D147_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D147 BerryEsseen.Upper0423.Covers.Data.DW147.accepted
attribute [kernel_fact] BerryOpt.D147.final
#print axioms BerryOpt.D147.final
