import NativeTrust
import BO_D208_Parse
import BO_D208_L0
import BO_D208_L1
import BO_D208_L2
import BO_D208_L3
import BO_D208_L4
import BO_D208_L5
import BO_D208_L6
import BO_D208_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D208 BerryEsseen.Upper0423.Covers.Data.DW208.accepted
attribute [kernel_fact] BerryOpt.D208.final
#print axioms BerryOpt.D208.final
