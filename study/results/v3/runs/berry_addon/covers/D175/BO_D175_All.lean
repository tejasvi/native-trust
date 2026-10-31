import NativeTrust
import BO_D175_Parse
import BO_D175_L0
import BO_D175_L1
import BO_D175_L2
import BO_D175_L3
import BO_D175_L4
import BO_D175_L5
import BO_D175_L6
import BO_D175_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D175 BerryEsseen.Upper0423.Covers.Data.DW175.accepted
attribute [kernel_fact] BerryOpt.D175.final
#print axioms BerryOpt.D175.final
