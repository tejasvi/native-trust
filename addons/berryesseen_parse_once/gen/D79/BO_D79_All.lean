import NativeTrust
import BO_D79_Parse
import BO_D79_L0
import BO_D79_L1
import BO_D79_L2
import BO_D79_L3
import BO_D79_L4
import BO_D79_L5
import BO_D79_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D79 BerryEsseen.Upper0423.Covers.Data.DW79.accepted
attribute [kernel_fact] BerryOpt.D79.final
#print axioms BerryOpt.D79.final
