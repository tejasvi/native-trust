import NativeTrust
import denote.yoco_goals.Goal4LateScopedBridge
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth denote.yoco_goals.Goal4LateScopedBridge 3 (config := { stage := true, csimp := true, propSplit := true, split := 16, trace := true })
