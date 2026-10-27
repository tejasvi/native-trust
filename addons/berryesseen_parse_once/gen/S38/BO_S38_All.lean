import NativeTrust
import BO_S38_Parse
import BO_S38_L0
import BO_S38_L1
import BO_S38_L2
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S38 BerryEsseen.Upper0423.Small.Data.Cover38.accepted
attribute [kernel_fact] BerryOpt.S38.final
#print axioms BerryOpt.S38.final
