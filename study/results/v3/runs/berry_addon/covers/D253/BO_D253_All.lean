import NativeTrust
import BO_D253_Parse
import BO_D253_L0
import BO_D253_L1
import BO_D253_L2
import BO_D253_L3
import BO_D253_L4
import BO_D253_L5
import BO_D253_L6
import BO_D253_L7
import BO_D253_L8
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D253 BerryEsseen.Upper0423.Covers.Data.DW253.accepted
attribute [kernel_fact] BerryOpt.D253.final
#print axioms BerryOpt.D253.final
