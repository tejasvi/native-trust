import GroupCmd
import Veir.Interpreter.Memory
/-! B08 group (1): both `bv_decide` facts of `Veir.Interpreter.Memory` (0: loadByte64, 1: llvmLoad) converted together,
so that the rebuilt `llvmLoad`, `memcpy`, `memmove` use only converted facts. -/
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option Elab.async false
set_option bvs4.workdir "/home/ntbuild/work_bvscale/veir/sat"
set_option bvs4.log "/home/ntbuild/work_bvscale/groups/GMemory.progress"
bvs5_group "Veir.Interpreter.Memory:0,1"
