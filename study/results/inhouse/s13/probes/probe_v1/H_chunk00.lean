import NativeTrust
import S45Comp.FactsHints
import S45Data.T9Hint7
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe H_chunk00: the driver's per-fact step on the statement of `Sortnet.S45Data.T9Hint7Check.chunk00`
(S45Data/T9Hint7Check/Chunk00.lean), without building the chunk theorem natively. -/



open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START H_chunk00"
  let p ← elabTerm (← `(Sortnet.Facts.checkHints Sortnet.S45Data.theHint7Rec 0 813246 32 = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.S45Data.T9Hint7Check.chunk00._native.native_decide.ax_1_1
  let name := (`_s13probe).str "H_chunk00"
  let cfg : KernelConfig := { split := 8, trace := true, native := false }
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  try
    let r ← proveTrueSplit e name [] cfg (native? := some true)
    IO.println s!"PROVED `{ax}` as `{r.thm}`: kernel_ms={r.ms} copies={r.copies.size} \
      total_ms={(← IO.monoMsNow) - t0} pieces={r.pieces} axioms={(← collectAxioms r.thm).toList}"
  catch ex =>
    let msg := (← ex.toMessageData.toString).replace "\n" " | "
    IO.println s!"FAILED `{ax}`: total_ms={(← IO.monoMsNow) - t0} {msg}"
