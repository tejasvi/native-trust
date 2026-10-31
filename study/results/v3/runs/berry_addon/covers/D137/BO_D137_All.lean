import NativeTrust
import BO_D137_Parse
import BO_D137_L0
import BO_D137_L1
import BO_D137_L2
import BO_D137_L3
import BO_D137_L4
import BO_D137_L5
import BO_D137_L6
import BO_D137_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D137 BerryEsseen.Upper0423.Covers.Data.DW137.accepted
attribute [kernel_fact] BerryOpt.D137.final
#print axioms BerryOpt.D137.final
