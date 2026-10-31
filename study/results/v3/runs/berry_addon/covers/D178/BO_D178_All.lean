import NativeTrust
import BO_D178_Parse
import BO_D178_L0
import BO_D178_L1
import BO_D178_L2
import BO_D178_L3
import BO_D178_L4
import BO_D178_L5
import BO_D178_L6
import BO_D178_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D178 BerryEsseen.Upper0423.Covers.Data.DW178.accepted
attribute [kernel_fact] BerryOpt.D178.final
#print axioms BerryOpt.D178.final
