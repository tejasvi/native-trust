import NativeTrust
import BO_D222_Parse
import BO_D222_L0
import BO_D222_L1
import BO_D222_L2
import BO_D222_L3
import BO_D222_L4
import BO_D222_L5
import BO_D222_L6
import BO_D222_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D222 BerryEsseen.Upper0423.Covers.Data.DW222.accepted
attribute [kernel_fact] BerryOpt.D222.final
#print axioms BerryOpt.D222.final
