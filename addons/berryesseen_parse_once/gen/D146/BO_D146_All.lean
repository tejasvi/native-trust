import NativeTrust
import BO_D146_Parse
import BO_D146_L0
import BO_D146_L1
import BO_D146_L2
import BO_D146_L3
import BO_D146_L4
import BO_D146_L5
import BO_D146_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D146 BerryEsseen.Upper0423.Covers.Data.DW146.accepted
attribute [kernel_fact] BerryOpt.D146.final
#print axioms BerryOpt.D146.final
