import BVS.Driver6
import Veir.Passes.InstructionSelection.Proofs
/-! (b) veir fact 108: base check split across declarations (bit-blaster run, segments of 30000 nodes), sharded. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.workdir "/home/ntbuild/work_bvscale/veir/sat"
set_option bvs4.timeout 600
set_option bvs4.log "/home/ntbuild/work_bvscale/veir/b/VB108.progress"
bvs6_prep Veir.Passes.InstructionSelection.Proofs "/home/ntbuild/work_bvscale/veir/b" 4 30000 108
