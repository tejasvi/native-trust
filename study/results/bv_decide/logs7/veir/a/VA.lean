import BVS.Driver5
import Veir.Passes.InstructionSelection.Proofs
/-! (a) veir facts that timed out at 900 s in the sweep (one process): sshlSat (73), sdivwPow2_neg (88),
sdivwPow2_pos (89). Prepared here (data, base check, empty clause); chunks in VA_S*.lean; assembled and the
users rebuilt in VA_Final.lean. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.workdir "/home/ntbuild/work_bvscale/veir/sat"
set_option bvs4.timeout 600
set_option bvs4.log "/home/ntbuild/work_bvscale/veir/a/VA.progress"
bvs5_prep Veir.Passes.InstructionSelection.Proofs "/home/ntbuild/work_bvscale/veir/a" 4 73 88 89
