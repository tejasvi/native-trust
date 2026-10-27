import NativeTrust
import BO_D88_Parse
import BO_D88_L0
import BO_D88_L1
import BO_D88_L2
import BO_D88_L3
import BO_D88_L4
import BO_D88_L5
import BO_D88_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D88 BerryEsseen.Upper0423.Covers.Data.DW88.accepted
attribute [kernel_fact] BerryOpt.D88.final
#print axioms BerryOpt.D88.final
