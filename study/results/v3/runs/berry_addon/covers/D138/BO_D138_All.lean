import NativeTrust
import BO_D138_Parse
import BO_D138_L0
import BO_D138_L1
import BO_D138_L2
import BO_D138_L3
import BO_D138_L4
import BO_D138_L5
import BO_D138_L6
import BO_D138_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D138 BerryEsseen.Upper0423.Covers.Data.DW138.accepted
attribute [kernel_fact] BerryOpt.D138.final
#print axioms BerryOpt.D138.final
