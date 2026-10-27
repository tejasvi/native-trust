import NativeTrust
import BO_D209_Parse
import BO_D209_L0
import BO_D209_L1
import BO_D209_L2
import BO_D209_L3
import BO_D209_L4
import BO_D209_L5
import BO_D209_L6
import BO_D209_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D209 BerryEsseen.Upper0423.Covers.Data.DW209.accepted
attribute [kernel_fact] BerryOpt.D209.final
#print axioms BerryOpt.D209.final
