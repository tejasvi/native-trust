import NativeTrust
import BO_D134_Parse
import BO_D134_L0
import BO_D134_L1
import BO_D134_L2
import BO_D134_L3
import BO_D134_L4
import BO_D134_L5
import BO_D134_L6
import BO_D134_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D134 BerryEsseen.Upper0423.Covers.Data.DW134.accepted
attribute [kernel_fact] BerryOpt.D134.final
#print axioms BerryOpt.D134.final
