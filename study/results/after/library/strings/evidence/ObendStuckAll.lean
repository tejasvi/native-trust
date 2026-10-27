import NativeTrust
import Compiler.ObjectiveBendFrontEndAdequacy
import Compiler.ObjectiveBendSpecificationClosure
open Lean Meta Elab Term NativeTrust

/-! Probe: for each of the 13 ObjectiveBend facts, where the evaluation of the retry's
parametric term gets stuck (`findStuck`, kernel whnf). -/

set_option maxHeartbeats 0 in
run_elab do
  let names := [`Minidregg.Compiler.ObjectiveBendFrontEndAdequacy.accept_inhabited] ++
    ([`binary_self_accepted, `claim_spec_accepted, `empty_seed_accepted, `f_bound_mismatch_refused,
      `inherited_unprovided_refused, `non_boolean_claim_refused, `open_extension_reused_accepted,
      `requires_signature_refused, `twice_accepted, `unbound_self_member_refused,
      `unprovided_requirement_refused, `wrong_target_refused].map (`Minidregg.Compiler.ObjectiveBendSpecificationClosure ++ ·))
  for t in names do
    let some ci := (← getEnv).find? t | IO.eprintln s!"PROBE {t}: no theorem"; continue
    let e ← instantiateMVars (← mkDecide ci.type)
    let ccfg : CopyConfig := { wf := true, retryRepl := true, copyHeartbeats := 20000 }
    let t0 ← IO.monoMsNow
    try
      let pt ← Param.paramTerm e ccfg
      let n := pt.origs.size
      let args := (Array.range n).foldl (fun acc i => (acc.push pt.repls[i]!).push pt.eqs[i]!) #[]
      let e' := pt.E.beta args
      match ← findStuck e' 120000 with
      | some (s, via) =>
        IO.eprintln s!"PROBE {t.getString!}: stuck head={s.getAppFn.constName?.getD .anonymous} via={via} ms={(← IO.monoMsNow) - t0}"
      | none => IO.eprintln s!"PROBE {t.getString!}: no stuck point (value or budget) ms={(← IO.monoMsNow) - t0}"
    catch ex =>
      IO.eprintln s!"PROBE {t.getString!}: error {((← ex.toMessageData.toString).replace "\n" " ").take 200}"
