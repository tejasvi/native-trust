import NativeTrust
import BVS
import AsiStackProofs.StackBoundaries
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option bvs4.workdir "/home/ntbuild/v3/sweeps/bvs/facts/asi-stack-book/sat"
set_option bvs4.timeout 600
set_option bvs4.log "/home/ntbuild/v3/sweeps/bvs/facts/asi-stack-book/G_AsiStackProofs_StackBoundaries_0.progress"
bvs5_fact AsiStackProofs.StackBoundaries 0
