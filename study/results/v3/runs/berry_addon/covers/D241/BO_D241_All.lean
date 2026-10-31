import NativeTrust
import BO_D241_Parse
import BO_D241_L0
import BO_D241_L1
import BO_D241_L2
import BO_D241_L3
import BO_D241_L4
import BO_D241_L5
import BO_D241_L6
import BO_D241_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D241 BerryEsseen.Upper0423.Covers.Data.DW241.accepted
attribute [kernel_fact] BerryOpt.D241.final
#print axioms BerryOpt.D241.final
