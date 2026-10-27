import NativeTrust
import BO_D92_Parse
import BO_D92_L0
import BO_D92_L1
import BO_D92_L2
import BO_D92_L3
import BO_D92_L4
import BO_D92_L5
import BO_D92_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D92 BerryEsseen.Upper0423.Covers.Data.DW92.accepted
attribute [kernel_fact] BerryOpt.D92.final
#print axioms BerryOpt.D92.final
