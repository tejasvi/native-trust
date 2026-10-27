import NativeTrust
import S11Data
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe T_S_certOK_harder11: the driver's per-fact step on the statement of `Sortnet.certOK_harder11`
(S13/S11/Main.lean), without building the chunk theorem natively. -/

namespace Sortnet
open S11 S11Data

open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START T_S_certOK_harder11"
  let p ← elabTerm (← `(certOK theCert certCount 2048 11 35 = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.certOK_harder11._native.native_decide.ax_1_1
  let name := (`_s13probe).str "T_S_certOK_harder11"
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  let bs ← triageBlockers e
  IO.println s!"TRIAGE T_S_certOK_harder11: {bs.size} blocker(s), {(← IO.monoMsNow) - t0} ms"
  for b in bs do
    IO.println s!"BLOCKER T_S_certOK_harder11 {b.name} | {(b.reason.replace "\n" " ").take 160} | path {b.path}"

end Sortnet
