import NativeTrust
import BO_D238_Parse
import BO_D238_L0
import BO_D238_L1
import BO_D238_L2
import BO_D238_L3
import BO_D238_L4
import BO_D238_L5
import BO_D238_L6
import BO_D238_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D238 BerryEsseen.Upper0423.Covers.Data.DW238.accepted
attribute [kernel_fact] BerryOpt.D238.final
#print axioms BerryOpt.D238.final
