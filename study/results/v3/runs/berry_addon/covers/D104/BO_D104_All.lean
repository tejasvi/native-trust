import NativeTrust
import BO_D104_Parse
import BO_D104_L0
import BO_D104_L1
import BO_D104_L2
import BO_D104_L3
import BO_D104_L4
import BO_D104_L5
import BO_D104_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D104 BerryEsseen.Upper0423.Covers.Data.DW104.accepted
attribute [kernel_fact] BerryOpt.D104.final
#print axioms BerryOpt.D104.final
