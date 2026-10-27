import NativeTrust
import Lfzk.SoundnessAudit
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth Lfzk.SoundnessAudit 9 (config := { stage := true, csimp := true, propSplit := true, split := 16, trace := true })
