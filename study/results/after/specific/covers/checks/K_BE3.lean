import BoCore
import BerryEsseen.Upper0423.Covers.Data.BE3
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
bo_tree BerryOpt.BE3 BerryEsseen.Upper0423.Covers.Data.BE3.data
bo_parse BerryOpt.BE3 BerryEsseen.Upper0423.Covers.Data.BE3.accepted
bo_leaves BerryOpt.BE3 BerryEsseen.Upper0423.Covers.Data.BE3.accepted 0 100
bo_assemble BerryOpt.BE3 BerryEsseen.Upper0423.Covers.Data.BE3.accepted
#print axioms BerryOpt.BE3.final
