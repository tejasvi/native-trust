import NativeTrust
import BO_D184_Parse
import BO_D184_L0
import BO_D184_L1
import BO_D184_L2
import BO_D184_L3
import BO_D184_L4
import BO_D184_L5
import BO_D184_L6
import BO_D184_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D184 BerryEsseen.Upper0423.Covers.Data.DW184.accepted
attribute [kernel_fact] BerryOpt.D184.final
#print axioms BerryOpt.D184.final
