import NativeTrust
import BO_D196_Parse
import BO_D196_L0
import BO_D196_L1
import BO_D196_L2
import BO_D196_L3
import BO_D196_L4
import BO_D196_L5
import BO_D196_L6
import BO_D196_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D196 BerryEsseen.Upper0423.Covers.Data.DW196.accepted
attribute [kernel_fact] BerryOpt.D196.final
#print axioms BerryOpt.D196.final
