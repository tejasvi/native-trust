import NativeTrust
import BO_D73_Parse
import BO_D73_L0
import BO_D73_L1
import BO_D73_L2
import BO_D73_L3
import BO_D73_L4
import BO_D73_L5
import BO_D73_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D73 BerryEsseen.Upper0423.Covers.Data.DW73.accepted
attribute [kernel_fact] BerryOpt.D73.final
#print axioms BerryOpt.D73.final
