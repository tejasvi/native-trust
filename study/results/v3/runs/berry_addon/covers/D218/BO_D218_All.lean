import NativeTrust
import BO_D218_Parse
import BO_D218_L0
import BO_D218_L1
import BO_D218_L2
import BO_D218_L3
import BO_D218_L4
import BO_D218_L5
import BO_D218_L6
import BO_D218_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D218 BerryEsseen.Upper0423.Covers.Data.DW218.accepted
attribute [kernel_fact] BerryOpt.D218.final
#print axioms BerryOpt.D218.final
