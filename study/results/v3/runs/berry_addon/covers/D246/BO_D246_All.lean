import NativeTrust
import BO_D246_Parse
import BO_D246_L0
import BO_D246_L1
import BO_D246_L2
import BO_D246_L3
import BO_D246_L4
import BO_D246_L5
import BO_D246_L6
import BO_D246_L7
import BO_D246_L8
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D246 BerryEsseen.Upper0423.Covers.Data.DW246.accepted
attribute [kernel_fact] BerryOpt.D246.final
#print axioms BerryOpt.D246.final
