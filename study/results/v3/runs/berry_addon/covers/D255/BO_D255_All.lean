import NativeTrust
import BO_D255_Parse
import BO_D255_L0
import BO_D255_L1
import BO_D255_L2
import BO_D255_L3
import BO_D255_L4
import BO_D255_L5
import BO_D255_L6
import BO_D255_L7
import BO_D255_L8
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D255 BerryEsseen.Upper0423.Covers.Data.DW255.accepted
attribute [kernel_fact] BerryOpt.D255.final
#print axioms BerryOpt.D255.final
