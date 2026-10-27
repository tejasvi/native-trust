import Lean
import NativeTrust.Kernelize

/-!
# A write-time linter: will this native fact be kernel-checkable?

With `set_option linter.nativeTrust true`, every `native_decide`/`bv_decide`/`decide +native` fact
of the file is triaged statically as it is added (no evaluation, milliseconds): if a constant that
Lean's kernel cannot evaluate is reachable from the decided term, the linter warns and names it,
with the chain of definitions leading to it. Such a fact rests on compiled code for good: it can
never be re-proved by the kernel, independent checkers cannot check it, and `lake check` and
Comparator reject anything that uses it. Facts that pass the triage are kernel-checkable up to
resources (`kernelize`, `trust_check`, `kdecide`).

The triage over-approximates: a constant on a branch that the evaluation never takes still counts
(panic and trace messages, and proofs, are already excluded).
-/

open Lean Elab Command

namespace NativeTrust

register_option linter.nativeTrust : Bool := {
  defValue := false
  descr := "NativeTrust: warn when a native_decide/bv_decide fact can never be checked by Lean's \
    kernel (static triage of the constants it reaches)"
}

/-- Native axioms of the current file already triaged. -/
initialize lintState : IO.Ref NameSet ← IO.mkRef {}

def nativeTrustLinter : Linter where
  run := withSetOptionIn fun stx => do
    unless linter.nativeTrust.get (← getOptions) do return
    let env ← getEnv
    let mut done ← lintState.get
    let mut msgs : Array MessageData := #[]
    for (ax, ci) in env.constants.map₂.toList do
      unless isNativeAxiom env ax && !done.contains ax do continue
      done := done.insert ax
      let some (_, e, _) := ci.type.eq? | continue
      let blockers ← liftCoreM (findBlockers e (static := true))
      unless blockers.isEmpty do
        msgs := msgs.push <| m!"native fact `{privateToUserName ax}` can never be checked by \
          Lean's kernel: it reaches constants without a kernel definition\n" ++
          MessageData.joinSep (blockers.toList.map Blocker.toMessageData) "\n"
    lintState.set done
    unless msgs.isEmpty do
      logWarningAt stx (MessageData.joinSep msgs.toList "\n\n" ++
        m!"\n\nnote: this linter can be disabled with `set_option linter.nativeTrust false`")

initialize addLinter nativeTrustLinter

end NativeTrust
