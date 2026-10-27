import NativeTrust
import denote.yoco_goals.Goal4LateScopedBridge
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true
prove_native_axiom_nth denote.yoco_goals.Goal4LateScopedBridge 3 (config := { stage := true, csimp := true, propSplit := true, split := 16, trace := true })

open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let ns := env.constants.toList.filterMap fun (k, _) =>
    if k.toString.endsWith "goal4Late_pm_filter_eq._kernel.native_decide.ax_1_1" then some k else none
  if ns.isEmpty then logInfo "NOT FOUND"
  for n in ns do
    let axs ← liftCoreM (Lean.collectAxioms n)
    if axs.isEmpty then logInfo m!"'{n}' does not depend on any axioms"
    else logInfo m!"'{n}' depends on axioms: {axs.qsort Name.lt |>.toList}"
