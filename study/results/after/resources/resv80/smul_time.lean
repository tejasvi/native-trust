import NativeTrust
import Zcash.Snark.Fixtures.MultiAction.Honest.Fixture
open Lean Meta Elab Command NativeTrust

/-! Kernel time of single scalar multiplications from the zcash MSM `capturedMsm.evalNat capturedURS`
(MultiAction Honest fixture, `G = VestaG`): compiled code evaluates the term, NativeTrust's `reifyValue` turns the
value into an expression `v`, and the kernel checks the theorem `term = v` (proof `Eq.refl v`, so the kernel
evaluates the term). The MSM has 2^11 = 2048 such terms (plus `w`, `u` and `other`). -/

set_option maxHeartbeats 0
set_option maxRecDepth 100000
-- the kernel checks theorems in the elaboration thread (otherwise `addDecl` returns before the check)
set_option Elab.async false

elab "#kernel_time " id:ident t:term : command => liftTermElabM do
  let e ← Term.elabTerm t none
  Term.synthesizeSyntheticMVarsNoPostponing
  let e ← instantiateMVars e
  let T ← inferType e
  let t0 ← IO.monoMsNow
  match ← reifyValue e T with
  | .error m => logInfo m!"{id.getId}: no value: {m}"
  | .ok v =>
    let t1 ← IO.monoMsNow
    let ty ← mkEq e v
    let pf ← mkEqRefl v
    try
      withOptions (fun o => maxHeartbeats.set (Elab.async.set o false) 0) do
        addDecl (.thmDecl { name := id.getId, levelParams := [], type := ty, value := pf })
      logInfo m!"{id.getId}: compiled evaluation and reification {t1 - t0} ms; kernel check of `term = value` {(← IO.monoMsNow) - t1} ms"
    catch ex => logInfo m!"{id.getId}: kernel FAILED after {(← IO.monoMsNow) - t1} ms: {ex.toMessageData}"

open Zcash.Snark.Fixture2

#eval s!"scalar bit lengths: w {capturedMsm.wScalar.val.log2 + 1}, u {capturedMsm.uScalar.val.log2 + 1}, g5 {(capturedMsm.gScalars ⟨5, by decide⟩).val.log2 + 1}"
#kernel_time smulW capturedMsm.wScalar.val • capturedURS.w
#kernel_time smulU capturedMsm.uScalar.val • capturedURS.u
#kernel_time smulG5 (capturedMsm.gScalars ⟨5, by decide⟩).val • capturedURS.g ⟨5, by decide⟩
