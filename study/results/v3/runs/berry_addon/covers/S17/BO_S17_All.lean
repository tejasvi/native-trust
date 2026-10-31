import NativeTrust
import BO_S17_Parse
import BO_S17_L0
import BO_S17_L1
import BO_S17_L2
import BO_S17_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S17 BerryEsseen.Upper0423.Small.Data.Cover17.accepted
attribute [kernel_fact] BerryOpt.S17.final
#print axioms BerryOpt.S17.final
