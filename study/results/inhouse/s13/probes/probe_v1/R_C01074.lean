import NativeTrust
import S45Comp.Stage2.Fast
import S45Data.T9
import S45Data.T9Hint7
import S45Data.Stage2
set_option Elab.async false
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
set_option nativeTrust.eprint true

/-! Probe R_C01074: the driver's per-fact step on the statement of `Sortnet.Stage2.Run.c01074`
(S45Stage2Run/C01074.lean), without building the chunk theorem natively. -/



open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START R_C01074"
  let p ← elabTerm (← `(Sortnet.Stage2.rootsOKP Sortnet.S45Data.theT9Rec Sortnet.S45Data.theHint7Rec Sortnet.S45Data.theS2Data 278848 278865 = true)) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `Sortnet.Stage2.Run.c01074._native.native_decide.ax_1_1
  let name := (`_s13probe).str "R_C01074"
  let cfg : KernelConfig := { split := 8, trace := true, native := false }
  IO.println s!"STATEMENT_MS {(← IO.monoMsNow) - t0}"
  try
    let r ← proveTrueSplit e name [] cfg (native? := some true)
    IO.println s!"PROVED `{ax}` as `{r.thm}`: kernel_ms={r.ms} copies={r.copies.size} \
      total_ms={(← IO.monoMsNow) - t0} pieces={r.pieces} axioms={(← collectAxioms r.thm).toList}"
  catch ex =>
    let msg := (← ex.toMessageData.toString).replace "\n" " | "
    IO.println s!"FAILED `{ax}`: total_ms={(← IO.monoMsNow) - t0} {msg}"
