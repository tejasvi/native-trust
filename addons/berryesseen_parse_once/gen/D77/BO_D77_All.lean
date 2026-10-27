import NativeTrust
import BO_D77_Parse
import BO_D77_L0
import BO_D77_L1
import BO_D77_L2
import BO_D77_L3
import BO_D77_L4
import BO_D77_L5
import BO_D77_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D77 BerryEsseen.Upper0423.Covers.Data.DW77.accepted
attribute [kernel_fact] BerryOpt.D77.final
#print axioms BerryOpt.D77.final
