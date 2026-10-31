import NativeTrust
import BO_D206_Parse
import BO_D206_L0
import BO_D206_L1
import BO_D206_L2
import BO_D206_L3
import BO_D206_L4
import BO_D206_L5
import BO_D206_L6
import BO_D206_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D206 BerryEsseen.Upper0423.Covers.Data.DW206.accepted
attribute [kernel_fact] BerryOpt.D206.final
#print axioms BerryOpt.D206.final
