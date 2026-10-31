import NativeTrust
import BO_S24_Parse
import BO_S24_L0
import BO_S24_L1
import BO_S24_L2
import BO_S24_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S24 BerryEsseen.Upper0423.Small.Data.Cover24.accepted
attribute [kernel_fact] BerryOpt.S24.final
#print axioms BerryOpt.S24.final
