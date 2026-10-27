import NativeTrust
import BO_D151_Parse
import BO_D151_L0
import BO_D151_L1
import BO_D151_L2
import BO_D151_L3
import BO_D151_L4
import BO_D151_L5
import BO_D151_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D151 BerryEsseen.Upper0423.Covers.Data.DW151.accepted
attribute [kernel_fact] BerryOpt.D151.final
#print axioms BerryOpt.D151.final
