import NativeTrust
import BO_D176_Parse
import BO_D176_L0
import BO_D176_L1
import BO_D176_L2
import BO_D176_L3
import BO_D176_L4
import BO_D176_L5
import BO_D176_L6
import BO_D176_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D176 BerryEsseen.Upper0423.Covers.Data.DW176.accepted
attribute [kernel_fact] BerryOpt.D176.final
#print axioms BerryOpt.D176.final
