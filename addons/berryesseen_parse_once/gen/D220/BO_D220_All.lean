import NativeTrust
import BO_D220_Parse
import BO_D220_L0
import BO_D220_L1
import BO_D220_L2
import BO_D220_L3
import BO_D220_L4
import BO_D220_L5
import BO_D220_L6
import BO_D220_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D220 BerryEsseen.Upper0423.Covers.Data.DW220.accepted
attribute [kernel_fact] BerryOpt.D220.final
#print axioms BerryOpt.D220.final
