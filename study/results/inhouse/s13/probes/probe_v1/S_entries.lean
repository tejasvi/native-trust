import NativeTrust
import S45Comp.Stage2.Data
import S45Data.T9
import S45Data.Stage2
import S11Data
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe S_entries: the driver's per-fact step on the statement of `Sortnet.Stage2.Run.entries`
(S45Stage2Run/Entries.lean), without building the chunk theorem natively. -/



open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START S_entries"
  let p ← elabTerm (← `(Sortnet.Stage2.allEntriesOK Sortnet.S45Data.theT9Rec.count (fun i => Sortnet.Facts.natOfBytes (Sortnet.S45Data.theT9Rec.keyAt i)) Sortnet.S45Data.theT9Rec.valAt Sortnet.S45Data.theS2Data Sortnet.S11Data.theCert Sortnet.S11Data.certCount 20000 = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.Stage2.Run.entries._native.native_decide.ax_1_1
  let name := (`_s13probe).str "S_entries"
  let cfg : KernelConfig := { split := 8, trace := true, native := false }
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  try
    let r ← proveTrueSplit e name [] cfg (native? := some true)
    IO.println s!"PROVED `{ax}` as `{r.thm}`: kernel_ms={r.ms} copies={r.copies.size} \
      total_ms={(← IO.monoMsNow) - t0} pieces={r.pieces} axioms={(← collectAxioms r.thm).toList}"
  catch ex =>
    let msg := (← ex.toMessageData.toString).replace "\n" " | "
    IO.println s!"FAILED `{ax}`: total_ms={(← IO.monoMsNow) - t0} {msg}"
