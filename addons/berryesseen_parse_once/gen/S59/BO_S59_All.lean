import NativeTrust
import BO_S59_Parse
import BO_S59_L0
import BO_S59_L1
import BO_S59_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S59 BerryEsseen.Upper0423.Small.Data.Cover59.accepted
attribute [kernel_fact] BerryOpt.S59.final
#print axioms BerryOpt.S59.final
