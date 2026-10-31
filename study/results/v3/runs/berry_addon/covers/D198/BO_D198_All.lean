import NativeTrust
import BO_D198_Parse
import BO_D198_L0
import BO_D198_L1
import BO_D198_L2
import BO_D198_L3
import BO_D198_L4
import BO_D198_L5
import BO_D198_L6
import BO_D198_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D198 BerryEsseen.Upper0423.Covers.Data.DW198.accepted
attribute [kernel_fact] BerryOpt.D198.final
#print axioms BerryOpt.D198.final
