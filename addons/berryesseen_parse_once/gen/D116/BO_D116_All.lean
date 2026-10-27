import NativeTrust
import BO_D116_Parse
import BO_D116_L0
import BO_D116_L1
import BO_D116_L2
import BO_D116_L3
import BO_D116_L4
import BO_D116_L5
import BO_D116_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D116 BerryEsseen.Upper0423.Covers.Data.DW116.accepted
attribute [kernel_fact] BerryOpt.D116.final
#print axioms BerryOpt.D116.final
