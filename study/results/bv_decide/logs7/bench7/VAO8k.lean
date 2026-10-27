import BVS.Driver6
import AO8k
/-! andor_8192 with the split base check (Driver6): bit-blaster run, segments of 30000 nodes, chunks; 4 shards. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.workdir "/home/ntbuild/work_bvscale/satwork"
set_option bvs4.timeout 3000
set_option bvs4.log "/home/ntbuild/work_bvscale/bench7/VAO8k.progress"
bvs6_prep AO8k "/home/ntbuild/work_bvscale/bench7" 4 30000 0
