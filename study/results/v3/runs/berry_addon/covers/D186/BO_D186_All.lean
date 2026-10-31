import NativeTrust
import BO_D186_Parse
import BO_D186_L0
import BO_D186_L1
import BO_D186_L2
import BO_D186_L3
import BO_D186_L4
import BO_D186_L5
import BO_D186_L6
import BO_D186_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D186 BerryEsseen.Upper0423.Covers.Data.DW186.accepted
attribute [kernel_fact] BerryOpt.D186.final
#print axioms BerryOpt.D186.final
