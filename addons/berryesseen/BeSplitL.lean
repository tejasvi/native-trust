import NativeTrust
import BeList
import BeObs

/-!
# BerryEsseen: string-argument forms for splitting (list-level parser)

As `BeSplit`, but the tokens are parsed at the list level (`BeList`: `tokensL`, `parseCoverL`, no
`String` operation), which costs about 5 s and 1.2 GB for the largest cover data (85 KB), against about
3-4 ms and 3 MB of kernel memory per token for the package's String parser. Applied to a data literal,
NativeTrust rewrites `coverStringAccepted* … data` into `obsAccepted*L … [c₁, …]` and splits the
`List.all` over the cover's obligations. Import either this module or `BeSplit`, not both.
-/

namespace NativeTrust.BeSplitL

open BerryEsseen.Upper0423.Native NativeTrust.BeObs NativeTrust.BE

def obsAcceptedBEL (n : Nat) (blo bhi : Rat) (cs : List Char) : Bool :=
  (obsOfParse (obsBE n blo bhi 0 1) (parseCoverL 64 (tokensL cs))).all Ob.check

def obsAcceptedDWL (n : Nat) (dlo dhi : Rat) (cs : List Char) : Bool :=
  (obsOfParse (obs n dlo dhi 0 1) (parseCoverL 64 (tokensL cs))).all Ob.check

def obsAcceptedL (n : Nat) (cs : List Char) : Bool :=
  (obsOfParse (obs n 0 deltaMax 0 1) (parseCoverL 64 (tokensL cs))).all Ob.check

@[kernel_string_arg] theorem coverStringAcceptedBE_obsL (n : Nat) (blo bhi : Rat) (s : String) :
    coverStringAcceptedBE n blo bhi s = obsAcceptedBEL n blo bhi s.toList := by
  rw [coverStringAcceptedBE_eq]
  unfold coverListAcceptedBE obsAcceptedBEL
  generalize parseCoverL 64 (tokensL s.toList) = r
  rcases r with _ | ⟨cov, _ | ⟨t, ts⟩⟩ <;> simp [obsOfParse, Ob.check, coverAcceptedBE_eq_all]

@[kernel_string_arg] theorem coverStringAcceptedDW_obsL (n : Nat) (dlo dhi : Rat) (s : String) :
    coverStringAcceptedDW n dlo dhi s = obsAcceptedDWL n dlo dhi s.toList := by
  rw [coverStringAcceptedDW_eq]
  unfold coverListAcceptedDW obsAcceptedDWL
  generalize parseCoverL 64 (tokensL s.toList) = r
  rcases r with _ | ⟨cov, _ | ⟨t, ts⟩⟩ <;> simp [obsOfParse, Ob.check, coverAccepted_eq_all]

@[kernel_string_arg] theorem coverStringAccepted_obsL (n : Nat) (s : String) :
    coverStringAccepted n s = obsAcceptedL n s.toList := by
  rw [coverStringAccepted_eq]
  unfold coverListAccepted obsAcceptedL
  generalize parseCoverL 64 (tokensL s.toList) = r
  rcases r with _ | ⟨cov, _ | ⟨t, ts⟩⟩ <;> simp [obsOfParse, Ob.check, coverAccepted_eq_all]

end NativeTrust.BeSplitL

#print axioms NativeTrust.BeSplitL.coverStringAcceptedBE_obsL
#print axioms NativeTrust.BeSplitL.coverStringAcceptedDW_obsL
#print axioms NativeTrust.BeSplitL.coverStringAccepted_obsL
