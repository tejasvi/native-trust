import NativeTrust
import BO_D97_Parse
import BO_D97_L0
import BO_D97_L1
import BO_D97_L2
import BO_D97_L3
import BO_D97_L4
import BO_D97_L5
import BO_D97_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D97 BerryEsseen.Upper0423.Covers.Data.DW97.accepted
attribute [kernel_fact] BerryOpt.D97.final
#print axioms BerryOpt.D97.final
