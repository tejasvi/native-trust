import NativeTrust
import denote.yoco_goals.CanonicalGoal3L23Routing
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
prove_native_axiom_nth denote.yoco_goals.CanonicalGoal3L23Routing 21 (config := { split := 8 })
