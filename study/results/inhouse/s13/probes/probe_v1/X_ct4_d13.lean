import NativeTrust
import S45DataCt4.Data
import S45Comp.BFSChunk
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe X_ct4_d13: the driver's per-fact step on the statement of `Sortnet.S45.BFS.ct4_bfs_d13`
(S45DataCt4/Slice.lean), without building the chunk theorem natively. -/

namespace Sortnet.S45.BFS
open Sortnet.S45Data.Ct4

open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START X_ct4_d13"
  let p ← elabTerm (← `(bfsChunkLast dataByte 13 0 16 = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.S45.BFS.ct4_bfs_d13._native.native_decide.ax_1_1
  let name := (`_s13probe).str "X_ct4_d13"
  let cfg : KernelConfig := { split := 8, trace := true, native := false }
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  try
    let r ← proveTrueSplit e name [] cfg (native? := some true)
    IO.println s!"PROVED `{ax}` as `{r.thm}`: kernel_ms={r.ms} copies={r.copies.size} \
      total_ms={(← IO.monoMsNow) - t0} pieces={r.pieces} axioms={(← collectAxioms r.thm).toList}"
  catch ex =>
    let msg := (← ex.toMessageData.toString).replace "\n" " | "
    IO.println s!"FAILED `{ax}`: total_ms={(← IO.monoMsNow) - t0} {msg}"

end Sortnet.S45.BFS
