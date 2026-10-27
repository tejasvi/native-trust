import DY.ALaCarte.DecidableEq
import NativeTrust

/-!
# A cast-free decidable equality for DyLean's `ALaCarte.Container` (NativeTrust add-on)

`DY.ALaCarte.Container.decideEquality` is built with `rewrite [Subtype.mk.injEq]` and
`BareContainer.decideEquality` with `simp only [BareContainer.mk.injEq]` and `rewrite [← aux]`: both
cast a `Decidable` instance along an equation proved by `propext`, which the kernel cannot reduce
(`findStuck` reports the evaluation stuck at that cast). `decC` decides the same equality by structural
recursion, with no cast on `Decidable` (the only cast is along `id1 = id2` for two equal constructor ids,
which the kernel reduces). `Decidable p` is a subsingleton, so `decideEquality = decC` holds by
`Subsingleton.elim`, and `@[kernel_replace]` lets NativeTrust evaluate `decC` instead.
-/

namespace NTBob
open DY.ALaCarte

mutual
def decB {CtorId : Type} {ctors : Ctors CtorId} [DecidableEq CtorId] [∀ id, DecidableEq (ctors id).Data] :
    (x y : BareContainer ctors) → Decidable (x = y)
  | ⟨id1, d1, as1⟩, ⟨id2, d2, as2⟩ =>
    if h : id1 = id2 then
      match id2, d2, h with
      | _, d2, rfl =>
        match decEq d1 d2 with
        | isTrue hd =>
          match decA as1 as2 with
          | isTrue ha => isTrue (by subst hd; subst ha; rfl)
          | isFalse ha => isFalse (fun e => ha (by injection e))
        | isFalse hd => isFalse (fun e => hd (by injection e))
    else isFalse (fun e => h (by injection e))
def decA {CtorId : Type} {ctors : Ctors CtorId} [DecidableEq CtorId] [∀ id, DecidableEq (ctors id).Data] :
    (xs ys : Array (BareContainer ctors)) → Decidable (xs = ys)
  | ⟨l1⟩, ⟨l2⟩ =>
    match decL l1 l2 with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (fun e => h (by injection e))
def decL {CtorId : Type} {ctors : Ctors CtorId} [DecidableEq CtorId] [∀ id, DecidableEq (ctors id).Data] :
    (xs ys : List (BareContainer ctors)) → Decidable (xs = ys)
  | [], [] => isTrue rfl
  | [], _ :: _ => isFalse (fun e => by cases e)
  | _ :: _, [] => isFalse (fun e => by cases e)
  | x :: xs, y :: ys =>
    match decB x y with
    | isTrue hx =>
      match decL xs ys with
      | isTrue hxs => isTrue (by subst hx; subst hxs; rfl)
      | isFalse hxs => isFalse (fun e => hxs (List.cons.inj e).2)
    | isFalse hx => isFalse (fun e => hx (List.cons.inj e).1)
end

def decC {CtorId : Type} {ctors : Ctors CtorId} [DecidableEq CtorId] [∀ id, DecidableEq (ctors id).Data] :
    (x y : Container ctors) → Decidable (x = y)
  | ⟨v1, _⟩, ⟨v2, _⟩ =>
    match decB v1 v2 with
    | isTrue h => isTrue (by subst h; rfl)
    | isFalse h => isFalse (fun e => h (congrArg Subtype.val e))

@[kernel_replace]
theorem decideEquality_eq_decC : @Container.decideEquality = @decC := by
  funext CtorId ctors i1 i2 x y
  exact Subsingleton.elim _ _

end NTBob
