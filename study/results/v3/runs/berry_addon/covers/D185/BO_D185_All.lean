import NativeTrust
import BO_D185_Parse
import BO_D185_L0
import BO_D185_L1
import BO_D185_L2
import BO_D185_L3
import BO_D185_L4
import BO_D185_L5
import BO_D185_L6
import BO_D185_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D185 BerryEsseen.Upper0423.Covers.Data.DW185.accepted
attribute [kernel_fact] BerryOpt.D185.final
#print axioms BerryOpt.D185.final
