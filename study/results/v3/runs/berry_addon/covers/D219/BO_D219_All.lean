import NativeTrust
import BO_D219_Parse
import BO_D219_L0
import BO_D219_L1
import BO_D219_L2
import BO_D219_L3
import BO_D219_L4
import BO_D219_L5
import BO_D219_L6
import BO_D219_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D219 BerryEsseen.Upper0423.Covers.Data.DW219.accepted
attribute [kernel_fact] BerryOpt.D219.final
#print axioms BerryOpt.D219.final
