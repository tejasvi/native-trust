import NativeTrust
import BO_D223_Parse
import BO_D223_L0
import BO_D223_L1
import BO_D223_L2
import BO_D223_L3
import BO_D223_L4
import BO_D223_L5
import BO_D223_L6
import BO_D223_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D223 BerryEsseen.Upper0423.Covers.Data.DW223.accepted
attribute [kernel_fact] BerryOpt.D223.final
#print axioms BerryOpt.D223.final
