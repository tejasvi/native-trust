/-!
# Kernel-reducible well-founded recursion

Lean compiles well-founded recursion over a non-`Nat` measure to
`WellFounded.fix α C r (Lean.opaqueId wf) F`. The kernel cannot unfold `Lean.opaqueId`, so it
cannot evaluate such functions: `decide +kernel` gets stuck on `List.mergeSort`, for example,
while compiled code (`native_decide`) runs them.

`wfFix` is `WellFounded.fix` with the well-foundedness proof replaced by `accGen 64 wf`, which
unfolds to `2 ^ 64 - 1` layers of `Acc.intro` before it reaches `wf` (the construction of Coq's
`Acc_intro_generator`, originally due to Georges Gonthier). `WellFounded r` is a proposition, so
`wfFix` and `WellFounded.fix` are definitionally equal by proof irrelevance (`fix_eq_wfFix` is
`rfl`). Swapping one for the other inside a definition changes no statement and needs no axiom,
yet the kernel can now evaluate the recursion.

This works on Lean 4.35-4.36. Lean core is removing kernel reduction through accessibility
proofs (lean4 PR #14892, from v4.37). The durable route, used by default, is `fixFuel` below:
`WellFounded.fix` with fuel, proved equal to it from the unfolding equation alone.

This module imports nothing beyond `Init`; it is the only part of `NativeTrust` that generated
proofs depend on.
-/

namespace NativeTrust

universe u v

/-- A proof of `WellFounded r` that exposes `2 ^ n - 1` `Acc.intro` layers before it reaches `wf`
(the idea of Coq's `Acc_intro_generator`). Written with `Nat.rec` so that the kernel unfolds it
cheaply, and as a `def` rather than a `theorem`, because the kernel must unfold it and Lean core
is moving towards treating theorem bodies as opaque (lean4 PR #14896). -/
def accGen {α : Sort u} {r : α → α → Prop} (n : Nat) (wf : WellFounded r) : WellFounded r :=
  Nat.rec (motive := fun _ => WellFounded r → WellFounded r) (fun wf => wf)
    (fun _ ih wf => ⟨fun x => Acc.intro x (fun y _ =>
      WellFounded.rec (motive := fun _ => Acc r y) (fun h => h y) (ih (ih wf)))⟩) n wf

/-- `WellFounded.fix` with a lazily unfolding well-foundedness proof; the kernel can evaluate it
on closed arguments. It keeps `WellFounded.fix` as its head: then the kernel proves
`wfFix = WellFounded.fix` by comparing arguments (proof irrelevance) before unfolding anything.
Evaluation unfolds core's theorem `WellFounded.apply` and reduces `Acc.rec` on proofs: Lean's
kernel, `leanchecker` and nanoda accept that; `con-ron`/`con-leche` (`lake check --paranoid`),
which follow core's planned discipline of never reducing proofs, do not. The durable route is a
proved fuel-based replacement registered with `@[kernel_replace]`, which every checker accepts. -/
noncomputable def wfFix {α : Sort u} {C : α → Sort v} {r : α → α → Prop} (hwf : WellFounded r)
    (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  WellFounded.fix (accGen 64 hwf) F x

theorem wfFix_eq : @wfFix.{u, v} = @WellFounded.fix.{u, v} := rfl

theorem fix_eq_wfFix : @WellFounded.fix.{u, v} = @wfFix.{u, v} := rfl

/-! ## Fuel: the durable route

`fixFuelAux hwf F n` unfolds the functional `F` `n` times and then falls back to
`WellFounded.fix` itself. It agrees with `WellFounded.fix` for every `n`, by induction on `n` from
the unfolding equation `WellFounded.fix_eq` alone: no reduction of accessibility proofs, no
elimination of `Acc`. Lean core keeps that equation when it makes `WellFounded.fix` opaque to the
kernel (lean4 PR #14892), so `fix_eq_fixFuel` stays provable there. `fixFuel` uses `2 ^ 64` units
of fuel: the kernel evaluates `Nat.rec` on a literal lazily, one unfolding per recursive call
actually made, so the fallback is never reached on any evaluation that finishes. -/

/-- `n` unfoldings of `F`, then `WellFounded.fix`. -/
noncomputable def fixFuelAux {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
    (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (n : Nat) : ∀ x, C x :=
  Nat.rec (motive := fun _ => ∀ x, C x) (fun x => WellFounded.fix hwf F x)
    (fun _ ih x => F x (fun y _ => ih y)) n

/-- `WellFounded.fix` with `2 ^ 64` units of fuel; kernel-reducible on closed arguments. -/
noncomputable def fixFuel {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
    (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (x : α) : C x :=
  fixFuelAux hwf F 18446744073709551616 x

theorem fixFuelAux_eq {α : Sort u} {C : α → Sort v} {r : α → α → Prop}
    (hwf : WellFounded r) (F : ∀ x, (∀ y, r y x → C y) → C x) (n : Nat) (x : α) :
    fixFuelAux hwf F n x = WellFounded.fix hwf F x := by
  induction n generalizing x with
  | zero => rfl
  | succ n ih =>
    show F x (fun y _ => fixFuelAux hwf F n y) = WellFounded.fix hwf F x
    rw [WellFounded.fix_eq]
    congr 1
    funext y _
    exact ih y

theorem fix_eq_fixFuel : @WellFounded.fix.{u, v} = @fixFuel.{u, v} := by
  funext α C r hwf F x
  exact (fixFuelAux_eq hwf F _ x).symm

/-- Dependent congruence, for copies whose proofs are transported along the copy equations:
`F a rfl = F b h` for a function of a point and of an equation from `a` to it. -/
theorem congr_dep {α : Sort u} {β : Sort v} {a : α} (F : (x : α) → a = x → β) {b : α}
    (h : a = b) : F a rfl = F b h :=
  @Eq.rec α a (fun x hx => F a rfl = F x hx) rfl b h

/-! Lemmas used to assemble split kernel checks. -/

theorem all_append_true {α : Type u} {p : α → Bool} {l₁ l₂ : List α}
    (h₁ : l₁.all p = true) (h₂ : l₂.all p = true) : (l₁ ++ l₂).all p = true := by
  rw [List.all_append, h₁, h₂]; rfl

theorem all_take_drop_true {α : Type u} {p : α → Bool} {l : List α} {k : Nat}
    (h₁ : (l.take k).all p = true) (h₂ : (l.drop k).all p = true) : l.all p = true := by
  rw [← List.take_append_drop k l]; exact all_append_true h₁ h₂

theorem and_true_of {a b : Bool} (ha : a = true) (hb : b = true) : (a && b) = true := by
  rw [ha, hb]; rfl

theorem decide_eq_true_of {b : Bool} {inst : Decidable (b = true)} (h : b = true) :
    @decide (b = true) inst = true :=
  decide_eq_true h

end NativeTrust
