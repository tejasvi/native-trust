import NativeTrust
import BO_D211_Parse
import BO_D211_L0
import BO_D211_L1
import BO_D211_L2
import BO_D211_L3
import BO_D211_L4
import BO_D211_L5
import BO_D211_L6
import BO_D211_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D211 BerryEsseen.Upper0423.Covers.Data.DW211.accepted
attribute [kernel_fact] BerryOpt.D211.final
#print axioms BerryOpt.D211.final
