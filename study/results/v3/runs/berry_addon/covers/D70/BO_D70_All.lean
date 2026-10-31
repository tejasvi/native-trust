import NativeTrust
import BO_D70_Parse
import BO_D70_L0
import BO_D70_L1
import BO_D70_L2
import BO_D70_L3
import BO_D70_L4
import BO_D70_L5
import BO_D70_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D70 BerryEsseen.Upper0423.Covers.Data.DW70.accepted
attribute [kernel_fact] BerryOpt.D70.final
#print axioms BerryOpt.D70.final
