import NativeTrust
import BO_D76_Parse
import BO_D76_L0
import BO_D76_L1
import BO_D76_L2
import BO_D76_L3
import BO_D76_L4
import BO_D76_L5
import BO_D76_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D76 BerryEsseen.Upper0423.Covers.Data.DW76.accepted
attribute [kernel_fact] BerryOpt.D76.final
#print axioms BerryOpt.D76.final
