import BVS.Driver5
import Veir.Passes.InstructionSelection.Proofs
/-! (a) rerun of fact 89 with the final sources (build10) and per-chunk progress logging, one fact per pipeline. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.workdir "/home/ntbuild/work_bvscale/veir/sat"
set_option bvs4.timeout 600
set_option bvs4.log "/home/ntbuild/work_bvscale/veir/a2/VA89.progress"
bvs5_prep Veir.Passes.InstructionSelection.Proofs "/home/ntbuild/work_bvscale/veir/a2" 4 89
