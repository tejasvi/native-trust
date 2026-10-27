import NativeTrust
import S11Small
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe T_X_certOK_5: the driver's per-fact step on the statement of `Sortnet.certOK_5`
(S13/S11/Small.lean), without building the chunk theorem natively. -/

namespace Sortnet
open S11 S11Small

open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START T_X_certOK_5"
  let p ← elabTerm (← `(certOK cert5 count5 256 5 9 = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.certOK_5._native.native_decide.ax_1_1
  let name := (`_s13probe).str "T_X_certOK_5"
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  let bs ← triageBlockers e
  IO.println s!"TRIAGE T_X_certOK_5: {bs.size} blocker(s), {(← IO.monoMsNow) - t0} ms"
  for b in bs do
    IO.println s!"BLOCKER T_X_certOK_5 {b.name} | {(b.reason.replace "\n" " ").take 160} | path {b.path}"

end Sortnet
