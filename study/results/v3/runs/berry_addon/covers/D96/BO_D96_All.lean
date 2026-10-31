import NativeTrust
import BO_D96_Parse
import BO_D96_L0
import BO_D96_L1
import BO_D96_L2
import BO_D96_L3
import BO_D96_L4
import BO_D96_L5
import BO_D96_L6
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D96 BerryEsseen.Upper0423.Covers.Data.DW96.accepted
attribute [kernel_fact] BerryOpt.D96.final
#print axioms BerryOpt.D96.final
