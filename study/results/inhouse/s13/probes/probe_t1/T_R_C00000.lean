import NativeTrust
import S45Comp.Stage2.Fast
import S45Data.T9
import S45Data.T9Hint7
import S45Data.Stage2
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe T_R_C00000: the driver's per-fact step on the statement of `Sortnet.Stage2.Run.c00000`
(S45Stage2Run/C00000.lean), without building the chunk theorem natively. -/



open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START T_R_C00000"
  let p ← elabTerm (← `(Sortnet.Stage2.rootsOKP Sortnet.S45Data.theT9Rec Sortnet.S45Data.theHint7Rec Sortnet.S45Data.theS2Data 0 2875 = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.Stage2.Run.c00000._native.native_decide.ax_1_1
  let name := (`_s13probe).str "T_R_C00000"
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  let bs ← triageBlockers e
  IO.println s!"TRIAGE T_R_C00000: {bs.size} blocker(s), {(← IO.monoMsNow) - t0} ms"
  for b in bs do
    IO.println s!"BLOCKER T_R_C00000 {b.name} | {(b.reason.replace "\n" " ").take 160} | path {b.path}"
