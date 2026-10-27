import NativeTrust

/-!
# Cast retry (`NativeTrust.CastFree`), without Mathlib

Each fact below is decided by an instance whose kernel evaluation gets stuck at a cast along an
equality whose two sides are not definitionally equal (`propext`, `Quot.sound`). With the cast retry
(`KernelConfig.castRetry`, on by default) NativeTrust builds a cast-free version of the instance, proves
it equal by `funext` and `Subsingleton.elim`, and evaluates again; without it, the evaluation fails.

* rule 1: an instance built by `cases … <;> simp … <;> infer_instance` (as in asi-stack-book);
* rule 2: the derived `DecidableEq` of a structure with a quotient field (as `Nat.Partition`);
* rule 4: an instance built by `rw [propext …]; infer_instance`;
* no rule: an instance cast along a proof of another shape is reported as before.
-/

namespace CastRetryTest

/-! ## Rule 1 -/

inductive Stage | idle | busy | done
  deriving DecidableEq

inductive Kind | start | finish | reset
  deriving DecidableEq

structure St where
  stage : Stage
  count : Nat
  deriving DecidableEq

structure Ev where
  kind : Kind
  limit : Nat
  ok : Bool

def Valid (s : St) (e : Ev) : Prop :=
  s.count ≤ e.limit ∧ e.ok = true ∧
    match s.stage, e.kind with
    | .idle, .start => True
    | .busy, .finish => 0 < s.count
    | _, .reset => True
    | _, _ => False

instance validDec (s : St) (e : Ev) : Decidable (Valid s e) := by
  cases hs : s.stage <;> cases hk : e.kind <;> simp [Valid, hs, hk] <;> infer_instance

def next : Kind → Stage
  | .start => .busy
  | .finish => .done
  | .reset => .idle

def step (s : St) (e : Ev) : Option St :=
  if Valid s e then some { stage := next e.kind, count := s.count + 1 } else none

def run (s : St) : List Ev → Option St
  | [] => some s
  | e :: es => match step s e with
    | some s' => run s' es
    | none => none

def fact1 : Bool :=
  decide (run ⟨.idle, 0⟩ [⟨.start, 5, true⟩, ⟨.finish, 5, true⟩] = some ⟨.done, 2⟩)

/-! ## Rule 2 -/

def mod3 : Setoid Nat where
  r a b := a % 3 = b % 3
  iseqv := ⟨fun _ => rfl, fun h => h.symm, fun h₁ h₂ => h₁.trans h₂⟩

instance (a b : Nat) : Decidable (@HasEquiv.Equiv Nat (@instHasEquivOfSetoid Nat mod3) a b) :=
  inferInstanceAs (Decidable (a % 3 = b % 3))

structure Res where
  val : Quotient mod3
  tag : Bool
  deriving DecidableEq

def fact2 : Bool := decide ((⟨Quotient.mk mod3 1, true⟩ : Res) = ⟨Quotient.mk mod3 4, true⟩)

def fact2' : Bool := decide ((⟨Quotient.mk mod3 1, true⟩ : Res) ≠ ⟨Quotient.mk mod3 5, true⟩)

/-! ## Rule 4 -/

def Even' (n : Nat) : Prop := ∃ k, n = 2 * k

theorem even'_eq (n : Nat) : Even' n = (n % 2 = 0) :=
  propext ⟨fun ⟨k, hk⟩ => by omega, fun h => ⟨n / 2, by omega⟩⟩

instance even'Dec (n : Nat) : Decidable (Even' n) := by
  rw [even'_eq]; infer_instance

def fact4 : Bool := decide (Even' 10 ∧ ¬ Even' 7)

/-! ## No rule applies -/

def Odd' (n : Nat) : Prop := ∃ k, n = 2 * k + 1

theorem odd'_dec_eq (n : Nat) : Decidable (Odd' n) = Decidable (n % 2 = 1) := by
  rw [show Odd' n = (n % 2 = 1) from propext ⟨fun ⟨k, hk⟩ => by omega, fun h => ⟨n / 2, by omega⟩⟩]

instance odd'Dec (n : Nat) : Decidable (Odd' n) :=
  cast (odd'_dec_eq n).symm inferInstance

def factNo : Bool := decide (Odd' 7)

/-! ## Checks -/

open Lean Meta NativeTrust in
def check (c : Name) (retry : Bool) : MetaM String := do
  let name := (`_castRetryTest ++ c).appendIndexAfter (if retry then 1 else 0)
  try
    let r ← proveTrueByKernel (mkConst c) name [] { native := false, castRetry := retry }
    return s!"proved; axioms {(← collectAxioms r.thm).toList}"
  catch _ => return "failed"

open Lean Meta NativeTrust in
#eval show MetaM Unit from do
  for c in [``validDec, ``instDecidableEqRes, ``even'Dec, ``odd'Dec] do
    IO.println s!"{c}: rule {(← synthCastFree? c).map (·.2)}"
  for c in [``fact1, ``fact2, ``fact2', ``fact4, ``factNo] do
    IO.println s!"{c}: castRetry=false {← check c false}; castRetry=true {← check c true}"

/-! The user-facing tactic, with the cast retry on by default. -/

theorem t1 : run ⟨.idle, 0⟩ [⟨.start, 5, true⟩, ⟨.finish, 5, true⟩] = some ⟨.done, 2⟩ := by kdecide

theorem t2 : (⟨Quotient.mk mod3 1, true⟩ : Res) = ⟨Quotient.mk mod3 4, true⟩ := by kdecide

theorem t4 : Even' 10 ∧ ¬ Even' 7 := by kdecide

#print axioms t1
#print axioms t2
#print axioms t4

end CastRetryTest
