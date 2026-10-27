module

public meta import Lean
public meta import NativeTrust.KernelBudget

/-!
# Kernel first: `native_decide` that tries `decide +kernel` before compiled code

`import NativeTrust.KernelFirst` changes what every `native_decide` and `decide +native` in the
importing modules does, without editing any call:

1. a static triage (no evaluation, cached per term) looks for constants that the kernel cannot
   evaluate (well-founded recursion is not counted: it is often reachable only on branches that the
   evaluation never takes);
2. if there is none, the kernel evaluates `decide p` as `decide +kernel` does (same instance, same
   auxiliary lemma), within `nativeTrust.kernelHeartbeats` thousand heartbeats (deterministic);
3. if the kernel proves it, that is the proof: no native axiom, nothing trusted beyond the kernel;
4. otherwise the state is restored and Lean's own native path runs (`evalDecideCore` with
   `+native`, exactly what the built-in elaborator runs), so the call behaves as before. An info
   message at the call names the reason (`nativeTrust.kernelFirst.report`), and
   `#kernel_first_summary` lists the calls of the file.

Switch it off for a declaration or file with `set_option nativeTrust.kernelFirst false`.

The elaborators below are registered for the syntax kinds of `native_decide` and `decide`; Lean tries
non-builtin elaborators before the builtin ones. They never call `evalTactic` on the same syntax, so
the fallback cannot loop. `decide` without `+native` and calls with `+kernel` or `+revert` are left to
the built-in elaborator (`throwUnsupportedSyntax`).

This file is a `module` that imports only Lean and `NativeTrust.KernelBudget`, so module-system files
can import it too.
-/

public meta section

open Lean Meta Elab Tactic

namespace NativeTrust.KernelFirst

register_option nativeTrust.kernelFirst : Bool := {
  defValue := true
  descr := "NativeTrust.KernelFirst: native_decide/decide +native first try decide +kernel within \
    `nativeTrust.kernelHeartbeats`, and use compiled evaluation only when the kernel does not prove \
    the goal"
}

register_option nativeTrust.kernelFirst.report : Bool := {
  defValue := true
  descr := "NativeTrust.KernelFirst: an info message at each call that falls back to compiled \
    evaluation, with the reason"
}

/-- One `native_decide`/`decide +native` call handled in this process. -/
structure CallRecord where
  decl : Name
  pos : Option Position
  tactic : Name
  /-- Proved by the kernel (no native axiom). -/
  kernel : Bool
  ms : Nat
  reason : String

initialize callRecords : IO.Ref (Array CallRecord) ← IO.mkRef #[]

/-- As Lean's `decide` preprocessing: no metavariables, free variables only through `let`. -/
def preprocessProp (expectedType : Expr) : TermElabM Expr := do
  let mut t ← instantiateMVars expectedType
  if t.hasFVar then t ← zetaReduce t
  if t.hasMVar || t.hasFVar then
    throwError "kernel-first: the goal has metavariables or free variables"
  return t

/-- Why the kernel did not prove the goal, as a short text. -/
def verdictReason (budget : Nat) : PlainVerdict → String
  | .proved _ => ""
  | .budget ms => s!"`decide +kernel` did not finish within {budget} thousand heartbeats ({ms} ms)"
  | .resources m => s!"`decide +kernel` ran out of resources: {m}"
  | .notTrue m => s!"the kernel does not reduce the decision procedure to `true`: {m}"

/-- The kernel attempt, as `decide +kernel` (`Lean.Elab.Tactic.evalDecideCore.doKernel`) with a
static triage first and a heartbeat budget. Closes the main goal on success; returns the reason on
failure (the caller restores the state). -/
def tryKernel (tac : Name) (budget : Nat) : TacticM (Option String) := do
  let reason ← IO.mkRef (none : Option String)
  try
    closeMainGoalUsing tac fun expectedType _ => do
      let expectedType ← preprocessProp expectedType
      let pf ← mkDecideProof expectedType
      let s := pf.appFn!.appArg!
      let d ← instantiateMVars (mkApp2 (mkConst ``Decidable.decide) expectedType s)
      -- static triage: a constant without a kernel definition is reachable; fail without
      -- evaluating. Well-founded recursion is not counted here: it is often reachable only on
      -- branches that the evaluation never takes
      let blockers ← cachedPlainBlockers d
      unless blockers.isEmpty do
        let names := blockers.toList.map (s!"`{·}`")
        let env ← getEnv
        -- in a module-system file, definitions of imported modules without `@[expose]` are visible
        -- only as axioms
        let hidden := env.header.isModule && blockers.any fun c =>
          env.find? c matches some (.axiomInfo _) &&
            !([``Classical.choice, ``sorryAx, `Lean.ofReduceBool, `Lean.ofReduceNat,
              `Lean.trustCompiler].contains c)
        let note := if hidden then "; in this module-system file, imported definitions that are \
          not `@[expose]`d have no visible definition" else ""
        let msg := s!"blocked: reaches {", ".intercalate (names.take 3)} (no kernel definition{note})"
        plainAttempts.modify (·.insert (d, budget, maxRecDepth.get (← getOptions)) (.notTrue msg))
        reason.set (some msg)
        throwError msg
      let levelsInType := (collectLevelParams {} expectedType).params
      let lemmaLevels := (← Term.getLevelNames).reverse.filter levelsInType.contains
      let t0 ← IO.monoMsNow
      try
        let lemmaName ← withOptions (fun o => maxHeartbeats.set (Elab.async.set o false) budget) do
          mkAuxLemma lemmaLevels expectedType pf
        return mkConst lemmaName (lemmaLevels.map .param)
      catch ex =>
        let v ← classifyKernelFailure ex ((← IO.monoMsNow) - t0)
        plainAttempts.modify (·.insert (d, budget, maxRecDepth.get (← getOptions)) v)
        let mut why := verdictReason budget v
        if let .notTrue _ := v then
          if let some path ← wfPath? d then
            why := s!"well-founded recursion (`WellFounded.fix` via {" → ".intercalate ((path.take 4).map toString)}): \
              `decide +kernel` cannot evaluate it; NativeTrust's `kdecide` can"
        reason.set (some why)
        throw ex
    return none
  catch ex =>
    match ← reason.get with
    | some r => return some r
    | none => return some (firstLine (← ex.toMessageData.toString))

def kernelFirstCore (tac : Name) (cfg : Parser.Tactic.DecideConfig) (stx : Syntax) :
    TacticM Unit := do
  let opts ← getOptions
  if !nativeTrust.kernelFirst.get opts || cfg.kernel || cfg.revert then throwUnsupportedSyntax
  let budget := nativeTrust.kernelHeartbeats.get opts
  let decl := (← Term.getDeclName?).getD .anonymous
  let pos := stx.getPos?.map (← getFileMap).toPosition
  let s ← saveState
  let t0 ← IO.monoMsNow
  match ← tryKernel tac budget with
  | none =>
    let ms := (← IO.monoMsNow) - t0
    let r : CallRecord :=
      { decl := decl, pos := pos, tactic := tac, kernel := true, ms := ms, reason := "" }
    callRecords.modify (·.push r)
  | some reason =>
    s.restore (restoreInfo := true)
    let ms := (← IO.monoMsNow) - t0
    -- Lean's own native path, as the built-in elaborator runs it
    evalDecideCore tac { cfg with native := true, kernel := false }
    let r : CallRecord :=
      { decl := decl, pos := pos, tactic := tac, kernel := false, ms := ms, reason := reason }
    callRecords.modify (·.push r)
    if nativeTrust.kernelFirst.report.get opts then
      logInfoAt stx m!"kernel-first: {nativeTacticDisplay tac} used compiled evaluation: {reason}"

@[tactic Lean.Parser.Tactic.nativeDecide] def evalNativeDecideKernelFirst : Tactic := fun stx => do
  let cfg ← elabDecideConfig stx[1]
  kernelFirstCore `native_decide { cfg with native := true } stx

@[tactic Lean.Parser.Tactic.decide] def evalDecideNativeKernelFirst : Tactic := fun stx => do
  let cfg ← elabDecideConfig stx[1]
  unless cfg.native do throwUnsupportedSyntax
  kernelFirstCore `decide cfg stx

/-- `#kernel_first_summary` lists the `native_decide`/`decide +native` calls of this file that
`NativeTrust.KernelFirst` handled: how many the kernel proved, and each call that fell back to
compiled evaluation, with the reason. It waits for the asynchronous proofs of the file first. -/
syntax (name := kernelFirstSummaryCmd) "#kernel_first_summary" : command

open Command in
@[command_elab kernelFirstSummaryCmd] def elabKernelFirstSummary : CommandElab := fun _ => do
  -- `constants` waits for every asynchronous proof elaborated so far
  let env ← getEnv
  let nNative := env.constants.map₂.foldl (init := 0) fun n c ci =>
    if c.components.contains `_native && ci matches .axiomInfo _ then n + 1 else n
  let rs := (← callRecords.get).qsort fun a b => match a.pos, b.pos with
    | some p, some q => p.line < q.line || (p.line == q.line && p.column < q.column)
    | _, _ => a.decl.toString < b.decl.toString
  let ok := rs.filter (·.kernel)
  let fb := rs.filter (!·.kernel)
  let kms := ok.foldl (· + ·.ms) 0
  let lines := fb.toList.map fun r =>
    let at_ := match r.pos with | some p => s!"line {p.line}" | none => "?"
    s!"FALLBACK `{r.decl}` ({nativeTacticDisplay r.tactic}, {at_}): {r.reason}"
  logInfo m!"kernel-first: {rs.size} calls: {ok.size} proved by `decide +kernel` ({kms} ms in \
    total), {fb.size} used compiled evaluation; native axioms in this module: {nNative}\
    {String.join (lines.map ("\n" ++ ·))}"

end NativeTrust.KernelFirst
