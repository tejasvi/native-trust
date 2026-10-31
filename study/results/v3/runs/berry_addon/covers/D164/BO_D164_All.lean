import NativeTrust
import BO_D164_Parse
import BO_D164_L0
import BO_D164_L1
import BO_D164_L2
import BO_D164_L3
import BO_D164_L4
import BO_D164_L5
import BO_D164_L6
import BO_D164_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D164 BerryEsseen.Upper0423.Covers.Data.DW164.accepted
attribute [kernel_fact] BerryOpt.D164.final
#print axioms BerryOpt.D164.final
