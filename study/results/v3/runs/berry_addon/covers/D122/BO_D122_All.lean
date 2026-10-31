import NativeTrust
import BO_D122_Parse
import BO_D122_L0
import BO_D122_L1
import BO_D122_L2
import BO_D122_L3
import BO_D122_L4
import BO_D122_L5
import BO_D122_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D122 BerryEsseen.Upper0423.Covers.Data.DW122.accepted
attribute [kernel_fact] BerryOpt.D122.final
#print axioms BerryOpt.D122.final
