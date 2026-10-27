import NativeTrust
import BO_S21_Parse
import BO_S21_L0
import BO_S21_L1
import BO_S21_L2
import BO_S21_L3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_assemble BerryOpt.S21 BerryEsseen.Upper0423.Small.Data.Cover21.accepted
attribute [kernel_fact] BerryOpt.S21.final
#print axioms BerryOpt.S21.final
