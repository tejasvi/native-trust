import NativeTrust
import S45DataCt4.Data
import S45Comp.BFSChunk
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe T_X_ct4_d12: the driver's per-fact step on the statement of `Sortnet.S45.BFS.ct4_bfs_d12`
(S45DataCt4/Slice.lean), without building the chunk theorem natively. -/

namespace Sortnet.S45.BFS
open Sortnet.S45Data.Ct4

open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START T_X_ct4_d12"
  let p ← elabTerm (← `(bfsChunkLast dataByte 12 0 16 = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.S45.BFS.ct4_bfs_d12._native.native_decide.ax_1_1
  let name := (`_s13probe).str "T_X_ct4_d12"
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  let bs ← triageBlockers e
  IO.println s!"TRIAGE T_X_ct4_d12: {bs.size} blocker(s), {(← IO.monoMsNow) - t0} ms"
  for b in bs do
    IO.println s!"BLOCKER T_X_ct4_d12 {b.name} | {(b.reason.replace "\n" " ").take 160} | path {b.path}"

end Sortnet.S45.BFS
