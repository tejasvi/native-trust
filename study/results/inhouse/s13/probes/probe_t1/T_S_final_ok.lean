import NativeTrust
import S45DataMain
import S45Comp.BFSChunk
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe T_S_final_ok: the driver's per-fact step on the statement of `Sortnet.S45Final.Main.final_ok`
(S45Final/Main/Header.lean), without building the chunk theorem natively. -/

namespace Sortnet.S45Final.Main
open Sortnet.S45.BFS

open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START T_S_final_ok"
  let p ← elabTerm (← `(finalOK Sortnet.S45Data.Main.dataByte = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.S45Final.Main.final_ok._native.native_decide.ax_1_1
  let name := (`_s13probe).str "T_S_final_ok"
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  let bs ← triageBlockers e
  IO.println s!"TRIAGE T_S_final_ok: {bs.size} blocker(s), {(← IO.monoMsNow) - t0} ms"
  for b in bs do
    IO.println s!"BLOCKER T_S_final_ok {b.name} | {(b.reason.replace "\n" " ").take 160} | path {b.path}"

end Sortnet.S45Final.Main
