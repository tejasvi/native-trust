import NativeTrust
import BO_D74_Parse
import BO_D74_L0
import BO_D74_L1
import BO_D74_L2
import BO_D74_L3
import BO_D74_L4
import BO_D74_L5
import BO_D74_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D74 BerryEsseen.Upper0423.Covers.Data.DW74.accepted
attribute [kernel_fact] BerryOpt.D74.final
#print axioms BerryOpt.D74.final
