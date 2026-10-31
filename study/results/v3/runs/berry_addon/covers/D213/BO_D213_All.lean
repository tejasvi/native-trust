import NativeTrust
import BO_D213_Parse
import BO_D213_L0
import BO_D213_L1
import BO_D213_L2
import BO_D213_L3
import BO_D213_L4
import BO_D213_L5
import BO_D213_L6
import BO_D213_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D213 BerryEsseen.Upper0423.Covers.Data.DW213.accepted
attribute [kernel_fact] BerryOpt.D213.final
#print axioms BerryOpt.D213.final
