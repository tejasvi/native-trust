import NativeTrust
import BO_D233_Parse
import BO_D233_L0
import BO_D233_L1
import BO_D233_L2
import BO_D233_L3
import BO_D233_L4
import BO_D233_L5
import BO_D233_L6
import BO_D233_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D233 BerryEsseen.Upper0423.Covers.Data.DW233.accepted
attribute [kernel_fact] BerryOpt.D233.final
#print axioms BerryOpt.D233.final
