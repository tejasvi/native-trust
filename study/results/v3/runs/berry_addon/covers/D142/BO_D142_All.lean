import NativeTrust
import BO_D142_Parse
import BO_D142_L0
import BO_D142_L1
import BO_D142_L2
import BO_D142_L3
import BO_D142_L4
import BO_D142_L5
import BO_D142_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D142 BerryEsseen.Upper0423.Covers.Data.DW142.accepted
attribute [kernel_fact] BerryOpt.D142.final
#print axioms BerryOpt.D142.final
