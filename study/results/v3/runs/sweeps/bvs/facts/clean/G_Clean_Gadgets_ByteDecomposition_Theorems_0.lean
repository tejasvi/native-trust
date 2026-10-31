import NativeTrust
import BVS
import Clean.Gadgets.ByteDecomposition.Theorems
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option bvs4.workdir "/home/ntbuild/v3/sweeps/bvs/facts/clean/sat"
set_option bvs4.timeout 600
set_option bvs4.log "/home/ntbuild/v3/sweeps/bvs/facts/clean/G_Clean_Gadgets_ByteDecomposition_Theorems_0.progress"
bvs5_fact Clean.Gadgets.ByteDecomposition.Theorems 0
