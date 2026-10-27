import NativeTrust
import BO_D227_Parse
import BO_D227_L0
import BO_D227_L1
import BO_D227_L2
import BO_D227_L3
import BO_D227_L4
import BO_D227_L5
import BO_D227_L6
import BO_D227_L7
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.D227 BerryEsseen.Upper0423.Covers.Data.DW227.accepted
attribute [kernel_fact] BerryOpt.D227.final
#print axioms BerryOpt.D227.final
