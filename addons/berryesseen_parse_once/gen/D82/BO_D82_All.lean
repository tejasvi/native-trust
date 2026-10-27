import NativeTrust
import BO_D82_Parse
import BO_D82_L0
import BO_D82_L1
import BO_D82_L2
import BO_D82_L3
import BO_D82_L4
import BO_D82_L5
import BO_D82_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D82 BerryEsseen.Upper0423.Covers.Data.DW82.accepted
attribute [kernel_fact] BerryOpt.D82.final
#print axioms BerryOpt.D82.final
