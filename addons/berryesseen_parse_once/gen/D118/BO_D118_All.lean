import NativeTrust
import BO_D118_Parse
import BO_D118_L0
import BO_D118_L1
import BO_D118_L2
import BO_D118_L3
import BO_D118_L4
import BO_D118_L5
import BO_D118_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D118 BerryEsseen.Upper0423.Covers.Data.DW118.accepted
attribute [kernel_fact] BerryOpt.D118.final
#print axioms BerryOpt.D118.final
