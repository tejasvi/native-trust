import BerryEsseen.Upper0423.Native.CoverGen

/-!
# BerryEsseen: cover acceptance as a list of obligations

`coverAccepted*` walks a cover tree and conjoins, at each split node, the validity of the split point
and the acceptance of both subtrees. Stated as `List.all` over the list of obligations (split-point
tests and leaves), the check can be cut into pieces by NativeTrust's `split` (`List.all` over a
computed list: chunks `(l.drop a).take k`, one kernel declaration each), so the memory of one
declaration is bounded by a few leaves instead of the whole cover.
-/

namespace NativeTrust.BeObs

open BerryEsseen.Upper0423.Native

/-- One obligation of a cover check: a split-point test or a leaf. -/
inductive Ob where
  | cond (b : Bool)
  | leaf (b : Box) (d : LeafData)

def Ob.check : Ob → Bool
  | .cond b => b
  | .leaf b d => leafAccepted b d

/-- The obligations of `coverAcceptedBE`, in the order the check visits them. -/
def obsBE (n : Nat) : Rat → Rat → Rat → Rat → Cover → List Ob
  | bl, bh, el, eh, .leaf d => [.leaf (imageBoxBE n bl bh el eh d) d]
  | bl, bh, el, eh, .split axis m left right =>
    if axis then
      .cond (decide (el < m) && decide (m < eh)) :: (obsBE n bl bh el m left ++ obsBE n bl bh m eh right)
    else
      .cond (decide (bl < m) && decide (m < bh)) :: (obsBE n bl m el eh left ++ obsBE n m bh el eh right)

theorem coverAcceptedBE_eq_all (n : Nat) (bl bh el eh : Rat) (cov : Cover) :
    coverAcceptedBE n bl bh el eh cov = (obsBE n bl bh el eh cov).all Ob.check := by
  induction cov generalizing bl bh el eh with
  | leaf d => simp [coverAcceptedBE, obsBE, Ob.check]
  | split axis m l r ihl ihr =>
    cases axis <;> simp [coverAcceptedBE, obsBE, Ob.check, ihl, ihr, List.all_append, Bool.and_assoc]

/-- The obligations of `coverAccepted` (`(δ, w)` coordinates). -/
def obs (n : Nat) : Rat → Rat → Rat → Rat → Cover → List Ob
  | dl, dh, wl, wh, .leaf d => [.leaf (imageBox n dl dh wl wh d) d]
  | dl, dh, wl, wh, .split axis m left right =>
    if axis then
      .cond (decide (wl < m) && decide (m < wh)) :: (obs n dl dh wl m left ++ obs n dl dh m wh right)
    else
      .cond (decide (dl < m) && decide (m < dh)) :: (obs n dl m wl wh left ++ obs n m dh wl wh right)

theorem coverAccepted_eq_all (n : Nat) (dl dh wl wh : Rat) (cov : Cover) :
    coverAccepted n dl dh wl wh cov = (obs n dl dh wl wh cov).all Ob.check := by
  induction cov generalizing dl dh wl wh with
  | leaf d => simp [coverAccepted, obs, Ob.check]
  | split axis m l r ihl ihr =>
    cases axis <;> simp [coverAccepted, obs, Ob.check, ihl, ihr, List.all_append, Bool.and_assoc]

/-- The obligations of a parse result: the cover's, if the parse consumed every token. -/
def obsOfParse {τ : Type} (f : Cover → List Ob) : Option (Cover × List τ) → List Ob
  | some (cov, []) => f cov
  | _ => [.cond false]

theorem match_eq_all {τ : Type} (f : Cover → List Ob) (g : Cover → Bool)
    (hg : ∀ cov, g cov = (f cov).all Ob.check) (r : Option (Cover × List τ)) :
    (match r with
      | some (cov, []) => g cov
      | _ => false) = (obsOfParse f r).all Ob.check := by
  rcases r with _ | ⟨cov, _ | ⟨t, ts⟩⟩ <;> simp [obsOfParse, Ob.check, hg]

end NativeTrust.BeObs

#print axioms NativeTrust.BeObs.coverAcceptedBE_eq_all
#print axioms NativeTrust.BeObs.coverAccepted_eq_all
#print axioms NativeTrust.BeObs.match_eq_all
