import NativeTrust
import Host.Json
open Lean Meta Elab Term NativeTrust

/-! Probe: static blockers of the repin facts as the retry's copies would see them. -/

set_option maxHeartbeats 0 in
run_elab do
  for t in [`Minidregg.Host.Json.grainPolicy_repin_preserves_extensions, `Minidregg.Host.Json.grainPolicy_repin_wrong_pins_refused] do
    let some ci := (← getEnv).find? t | throwError "no theorem"
    let e ← instantiateMVars (← mkDecide ci.type)
    let e := foldApps (← getEnv) e
    let bs ← findBlockers e (static := true) (retryRepl := true)
    IO.eprintln s!"PROBE {t}: {bs.size} blockers"
    for b in bs do
      IO.eprintln s!"PROBE   {b.name}  via {(b.path.take 8).map toString}"
