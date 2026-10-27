import NativeTrust
import S45Data.T9Test
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe X_T9Test_table: the driver's per-fact step on the statement of `Sortnet.S45Data.T9Test.table_facts_ok`
(S45Data/T9Test.lean), without building the chunk theorem natively. -/

namespace Sortnet.S45Data.T9Test
open Sortnet Sortnet.Facts

open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START X_T9Test_table"
  let p ← elabTerm (← `(tableFacts = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.S45Data.T9Test.table_facts_ok._native.native_decide.ax_1_1
  let name := (`_s13probe).str "X_T9Test_table"
  let cfg : KernelConfig := { split := 8, trace := true, native := false }
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  try
    let r ← proveTrueSplit e name [] cfg (native? := some true)
    IO.println s!"PROVED `{ax}` as `{r.thm}`: kernel_ms={r.ms} copies={r.copies.size} \
      total_ms={(← IO.monoMsNow) - t0} pieces={r.pieces} axioms={(← collectAxioms r.thm).toList}"
  catch ex =>
    let msg := (← ex.toMessageData.toString).replace "\n" " | "
    IO.println s!"FAILED `{ax}`: total_ms={(← IO.monoMsNow) - t0} {msg}"

end Sortnet.S45Data.T9Test
