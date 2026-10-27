import NativeTrust
import BO_S53_Parse
import BO_S53_L0
import BO_S53_L1
import BO_S53_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S53 BerryEsseen.Upper0423.Small.Data.Cover53.accepted
attribute [kernel_fact] BerryOpt.S53.final
#print axioms BerryOpt.S53.final
