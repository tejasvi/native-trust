import NativeTrust
import BO_D221_Parse
import BO_D221_L0
import BO_D221_L1
import BO_D221_L2
import BO_D221_L3
import BO_D221_L4
import BO_D221_L5
import BO_D221_L6
import BO_D221_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D221 BerryEsseen.Upper0423.Covers.Data.DW221.accepted
attribute [kernel_fact] BerryOpt.D221.final
#print axioms BerryOpt.D221.final
