import NativeTrust
open NativeTrust
set_option Elab.async false

/-!
# The staged route and its axioms (`proveTrueStaged`)

With `stage := true` the decided term's closed subterms become auxiliary constants whose values are proved
separately; the fact is proved over the values (`<name>.staged`) and bridged back to the original term by
congruence. Like every other route, the staged route now checks that the bridged proof uses only the standard
axioms.

* `pos`: a staged fact that goes through the bridge: proved, with standard axioms only;
* `neg`: the same shape, but the staged function has a replacement registered on a theorem proved from an axiom
  that is not standard: refused, the axiom does not reach a proof (an axiom rather than `sorry`, whose warning
  is worded differently across toolchains);
* `nd1`: `kernelize` with staging on a `native_decide` theorem.
-/

namespace StageAxiomsTest

def fastSum (n : Nat) : Nat := n * (n - 1) / 2
def slowSum (n : Nat) : Nat := (List.range n).foldl (· + ·) 0
axiom slowSum_eq_ax : @slowSum = @fastSum
theorem slowSum_eq : @slowSum = @fastSum := slowSum_eq_ax
attribute [kernel_replace] slowSum_eq

open Lean Meta Elab Term NativeTrust in
def run (label : String) (stx : TSyntax `term) : TermElabM Unit := do
  let p ← elabTerm stx (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let name := (`_stageAxiomsTest).str label
  try
    let r ← proveTrueSplit e name [] { native := false, stage := true, quickHeartbeats := 0 }
    IO.println s!"{label}: proved; axioms {(← collectAxioms r.thm).toList}; \
      through the staged bridge: {(← getEnv).contains (name ++ `staged)}"
  catch ex =>
    let m ← ex.toMessageData.toString
    let reported : Bool := (m.splitOn "non-standard axioms [StageAxiomsTest.slowSum_eq_ax]").length > 1
    IO.println s!"{label}: failed; non-standard axioms reported: {reported}"

open Lean Elab Term in
#eval show TermElabM Unit from do run "pos" (← `((List.range 3000).foldl (· + ·) 0 = 4498500))

open Lean Elab Term in
#eval show TermElabM Unit from do run "neg" (← `(slowSum 3000 = 4498500))

theorem nd1 : (List.range 3000).foldl (· + ·) 0 = 4498500 := by native_decide

open Lean Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let r ← kernelizeOne { native := false, stage := true, quickHeartbeats := 0 } ``nd1 (``nd1 ++ `kernel) (soft := true)
  if r.startsWith "OK" then IO.println s!"kernelize nd1 (staged): OK; axioms {(← collectAxioms (``nd1 ++ `kernel)).toList}"
  else IO.println s!"kernelize nd1 (staged): FAILED"

end StageAxiomsTest
