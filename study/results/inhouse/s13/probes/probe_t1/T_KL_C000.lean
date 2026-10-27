import NativeTrust
import S45DataMain
import S45Comp.BFSChunk
import S45Comp.Facts9
import S45Data.T9
import S45Data.T9Hint7
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe T_KL_C000: the driver's per-fact step on the statement of `Sortnet.S45Final.Main.Kl.C000.kl`
(S45Final/Main/Kl/C000.lean), without building the chunk theorem natively. -/

namespace Sortnet.S45Final.Main.Kl.C000
open Sortnet.S45.BFS

open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START T_KL_C000"
  let p ← elabTerm (← `(klChunk Sortnet.S45Data.Main.dataByte (Sortnet.Facts.fact9 Sortnet.S45Data.theT9Rec Sortnet.S45Data.theHint7Rec) Sortnet.Facts.St9.init 0 31000 485 = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.S45Final.Main.Kl.C000.kl._native.native_decide.ax_1_1
  let name := (`_s13probe).str "T_KL_C000"
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  let bs ← triageBlockers e
  IO.println s!"TRIAGE T_KL_C000: {bs.size} blocker(s), {(← IO.monoMsNow) - t0} ms"
  for b in bs do
    IO.println s!"BLOCKER T_KL_C000 {b.name} | {(b.reason.replace "\n" " ").take 160} | path {b.path}"

end Sortnet.S45Final.Main.Kl.C000
