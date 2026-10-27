import StrRepl
import StrReplace
import SplitOnSpace
import BerryEsseen.Upper0423.Native.CoverGen
set_option Elab.async false

/-!
# List-level form of the BerryEsseen cover parser

`coverStringAccepted*` parse a long string literal with `String.replace`, `String.splitOn`,
`String.toNat?` and `String.toInt?`, which the kernel cannot evaluate cheaply. The definitions here
redo the whole parse on `List Char` (no `String` operation, no string literal, structural recursion
or explicit `Nat` fuel only); the numeric results and the acceptance checks are the original ones.
The three `*_eq` theorems state that the original predicates equal the list-level ones on
`s.toList`.
-/

namespace NativeTrust.BE

open BerryEsseen.Upper0423.Native
open NativeTrust.StrRepl (toNatOfList? toIntOfSlice?)

/-! ### List-level definitions -/

/-- One pass of the tokenizer; `acc` is the current token, reversed. -/
def tokGo : List Char → List Char → List (List Char)
  | [], acc => if acc.isEmpty then [] else [acc.reverse]
  | c :: cs, acc =>
    if c = ' ' then (if acc.isEmpty then tokGo cs [] else acc.reverse :: tokGo cs [])
    else if c = '\n' then (if acc.isEmpty then tokGo cs [] else acc.reverse :: tokGo cs [])
    else tokGo cs (c :: acc)
termination_by structural cs _ => cs

/-- Split on `' '` and `'\n'` and drop the empty pieces, in one pass (mirrors `tokens`; the
`splitOn`/`filter` form is `tokensL_eq`). -/
def tokensL (cs : List Char) : List (List Char) := tokGo cs []

/-- `String.toInt?` on a character list: an optional leading `'-'`, then `toNatOfList?`. -/
def toIntL? : List Char → Option Int
  | [] => (toNatOfList? []).map Int.ofNat
  | c :: rest =>
    if c = '-' then (toNatOfList? rest).map Int.negOfNat
    else (toNatOfList? (c :: rest)).map Int.ofNat

/-- Mirrors `parseNat`. -/
def parseNatL (cs : List Char) : Option Nat := toNatOfList? cs

/-- Mirrors `parseRat`. -/
def parseRatL (cs : List Char) : Option Rat :=
  match cs.splitOn '/' with
  | [a] => (toIntL? a).map fun z ↦ (z : Rat)
  | [a, b] =>
    match toIntL? a, parseNatL b with
    | some z, some d => if d = 0 then none else some ((z : Rat) / (d : Rat))
    | _, _ => none
  | _ => none

/-- Mirrors `parsePanels`. -/
def parsePanelsL : Nat → List (List Char) → Option (List (Rat × Choice) × List (List Char))
  | 0, ts => some ([], ts)
  | k + 1, r :: code :: ts =>
    match parseRatL r, parseNatL code, parsePanelsL k ts with
    | some q, some c, some (rest, ts') => some ((q, choiceOf c) :: rest, ts')
    | _, _, _ => none
  | _, _ => none
termination_by structural k _ => k

/-- Mirrors `parseEnds`. -/
def parseEndsL : Nat → List (List Char) → Option (List Rat × List (List Char))
  | 0, ts => some ([], ts)
  | k + 1, r :: ts =>
    match parseRatL r, parseEndsL k ts with
    | some q, some (rest, ts') => some (q :: rest, ts')
    | _, _ => none
  | _, _ => none
termination_by structural k _ => k

/-- The leaf branch of `parseCover` (after the token `F`). -/
def parseLeafL (c tau nl : List Char) (ts : List (List Char)) :
    Option (Cover × List (List Char)) :=
  match parseRatL c, parseRatL tau, parseNatL nl with
  | some cq, some tq, some kl =>
    match parsePanelsL kl ts with
    | some (low, nh :: ts1) =>
      match parseNatL nh with
      | some kh =>
        match parsePanelsL kh ts1 with
        | some (high, nn :: ts2) =>
          match parseNatL nn with
          | some kn =>
            match parseEndsL kn ts2 with
            | some (normal, ts3) => some (.leaf ⟨cq, tq, low, high, normal⟩, ts3)
            | none => none
          | none => none
        | _ => none
      | none => none
    | _ => none
  | _, _, _ => none

/-- Mirrors `parseCover` (structural recursion on the fuel). -/
def parseCoverL : Nat → List (List Char) → Option (Cover × List (List Char))
  | 0, _ => none
  | _ + 1, [] => none
  | fuel + 1, t :: ts =>
    if t = ['S'] then
      match ts with
      | axis :: m :: ts =>
        match parseRatL m, parseCoverL fuel ts with
        | some mq, some (left, ts') =>
          match parseCoverL fuel ts' with
          | some (right, ts'') => some (.split (axis == ['1']) mq left right, ts'')
          | none => none
        | _, _ => none
      | _ => none
    else if t = ['F'] then
      match ts with
      | c :: tau :: nl :: ts => parseLeafL c tau nl ts
      | _ => none
    else none
termination_by structural fuel _ => fuel

def coverListAccepted (n : Nat) (cs : List Char) : Bool :=
  match parseCoverL 64 (tokensL cs) with
  | some (cov, []) => coverAccepted n 0 deltaMax 0 1 cov
  | _ => false

def coverListAcceptedDW (n : Nat) (dlo dhi : Rat) (cs : List Char) : Bool :=
  match parseCoverL 64 (tokensL cs) with
  | some (cov, []) => coverAccepted n dlo dhi 0 1 cov
  | _ => false

def coverListAcceptedBE (n : Nat) (blo bhi : Rat) (cs : List Char) : Bool :=
  match parseCoverL 64 (tokensL cs) with
  | some (cov, []) => coverAcceptedBE n blo bhi 0 1 cov
  | _ => false

/-! ### Proofs -/

/-- Map the remaining tokens of a parse result back to strings. -/
def mapRest {α : Type} (p : α × List (List Char)) : α × List String :=
  (p.1, p.2.map String.ofList)

@[simp] theorem mapRest_mk {α : Type} (a : α) (l : List (List Char)) :
    mapRest (a, l) = (a, l.map String.ofList) := rfl

theorem isEmpty_ofList (t : List Char) : (String.ofList t).isEmpty = t.isEmpty := by
  rw [Bool.eq_iff_iff, String.isEmpty_iff, String.ofList_eq_empty_iff, List.isEmpty_iff]

theorem tokGo_eq : ∀ (cs acc : List Char),
    tokGo cs acc = (List.splitOnPPrepend (· == ' ')
      (cs.map fun c => if c = '\n' then ' ' else c) acc).filter (fun t => !t.isEmpty)
  | [], acc => by
    cases acc <;> simp [tokGo]
  | c :: cs, acc => by
    have ih1 := tokGo_eq cs []
    rw [List.splitOnPPrepend_nil_right] at ih1
    have ih2 := tokGo_eq cs (c :: acc)
    by_cases h1 : c = ' '
    · subst h1
      cases acc <;> simp [tokGo, List.splitOnPPrepend_cons_eq_ite,
        List.splitOnP_cons_eq_ite_splitOnPPrepend, ih1]
    · by_cases h2 : c = '\n'
      · subst h2
        cases acc <;> simp [tokGo, List.splitOnPPrepend_cons_eq_ite,
          List.splitOnP_cons_eq_ite_splitOnPPrepend, ih1]
      · cases acc <;> simp [tokGo, List.splitOnPPrepend_cons_eq_ite,
          List.splitOnP_cons_eq_ite_splitOnPPrepend, h1, h2, ih2]

theorem tokensL_eq (cs : List Char) : tokensL cs =
    ((cs.map fun c => if c = '\n' then ' ' else c).splitOn ' ').filter fun t => !t.isEmpty := by
  rw [tokensL, tokGo_eq, List.splitOnPPrepend_nil_right]
  rfl

theorem tokens_eq (s : String) : tokens s = (tokensL s.toList).map String.ofList := by
  rw [tokensL_eq]
  unfold tokens
  rw [NativeTrust.StrFast.splitOn_space, NativeTrust.StrFast.toList_replace_newline,
    List.filter_map]
  congr 1
  apply List.filter_congr
  intro t _
  simp only [Function.comp, isEmpty_ofList]

theorem toIntOfSlice?_toSlice (s : String) : toIntOfSlice? s.toSlice = toIntL? s.toList := by
  unfold toIntOfSlice?
  rcases h : s.toSlice.dropPrefix? '-' with _ | rest
  · have h2 := String.Slice.dropPrefix?_eq_none_iff.1 h
    rw [String.Slice.startsWith_char_eq_head?, String.copy_toSlice] at h2
    simp only [String.copy_toSlice]
    rcases hl : s.toList with _ | ⟨c, cs⟩
    · rfl
    · rw [hl] at h2
      have hc : ¬ c = '-' := by
        intro hc
        subst hc
        simp at h2
      simp only [toIntL?, hc, ite_false]
  · have h2 := String.Slice.eq_append_of_dropPrefix?_char_eq_some h
    rw [String.copy_toSlice] at h2
    have hl : s.toList = '-' :: rest.copy.toList := by
      rw [h2, String.toList_append, String.toList_singleton]
      rfl
    rw [hl]
    simp only [toIntL?, ite_true]

theorem toInt?_ofList (cs : List Char) : (String.ofList cs).toInt? = toIntL? cs := by
  rw [NativeTrust.StrRepl.toInt?_eq, toIntOfSlice?_toSlice, String.toList_ofList]

theorem toNat?_ofList (cs : List Char) : (String.ofList cs).toNat? = toNatOfList? cs := by
  rw [NativeTrust.StrRepl.toNat?_eq_list, String.toList_ofList]

theorem parseNat_ofList (cs : List Char) : parseNat (String.ofList cs) = parseNatL cs := by
  unfold parseNat parseNatL
  exact toNat?_ofList cs

theorem parseRat_ofList (cs : List Char) : parseRat (String.ofList cs) = parseRatL cs := by
  unfold parseRat parseRatL
  rw [NativeTrust.StrFast.splitOn_slash, String.toList_ofList]
  rcases cs.splitOn '/' with _ | ⟨a, _ | ⟨b, _ | ⟨c, rest⟩⟩⟩
  · rfl
  · simp only [List.map_cons, List.map_nil, toInt?_ofList]
  · simp only [List.map_cons, List.map_nil, toInt?_ofList, toNat?_ofList, parseNatL]
    rcases toIntL? a with _ | z <;> rcases toNatOfList? b with _ | d <;> rfl
  · rfl

theorem parsePanels_map : ∀ (k : Nat) (ts : List (List Char)),
    parsePanels k (ts.map String.ofList) = (parsePanelsL k ts).map mapRest
  | 0, ts => by simp only [parsePanels, parsePanelsL, Option.map_some, mapRest_mk]
  | k + 1, [] => by
    rw [List.map_nil, parsePanels.eq_3]
    · rfl
    · simp
    · intro _ _ _ _ _ h; cases h
  | k + 1, [r] => by
    rw [List.map_cons, List.map_nil, parsePanels.eq_3]
    · rfl
    · simp
    · intro _ _ _ _ _ h; cases h
  | k + 1, r :: code :: ts => by
    rw [List.map_cons, List.map_cons, parsePanels.eq_2]
    simp only [parsePanelsL, parseRat_ofList, parseNat_ofList, parsePanels_map k ts]
    rcases parseRatL r with _ | q <;> rcases parseNatL code with _ | c <;>
      rcases parsePanelsL k ts with _ | ⟨rest, ts'⟩ <;> rfl

theorem parseEnds_map : ∀ (k : Nat) (ts : List (List Char)),
    parseEnds k (ts.map String.ofList) = (parseEndsL k ts).map mapRest
  | 0, ts => by simp only [parseEnds, parseEndsL, Option.map_some, mapRest_mk]
  | k + 1, [] => by
    rw [List.map_nil, parseEnds.eq_3]
    · rfl
    · simp
    · intro _ _ _ _ h; cases h
  | k + 1, r :: ts => by
    rw [List.map_cons, parseEnds.eq_2]
    simp only [parseEndsL, parseRat_ofList, parseEnds_map k ts]
    rcases parseRatL r with _ | q <;> rcases parseEndsL k ts with _ | ⟨rest, ts'⟩ <;> rfl

theorem ofList_S : String.ofList ['S'] = "S" := rfl
theorem ofList_F : String.ofList ['F'] = "F" := rfl

theorem ofList_eq_S_iff (t : List Char) : String.ofList t = "S" ↔ t = ['S'] := by
  rw [← ofList_S, String.ofList_inj]

theorem ofList_eq_F_iff (t : List Char) : String.ofList t = "F" ↔ t = ['F'] := by
  rw [← ofList_F, String.ofList_inj]

theorem ofList_beq_one (t : List Char) : (String.ofList t == "1") = (t == ['1']) := by
  rw [show ("1" : String) = String.ofList ['1'] from rfl, Bool.eq_iff_iff, beq_iff_eq, beq_iff_eq,
    String.ofList_inj]

theorem leaf_map (fuel : Nat) (c tau nl : List Char) (ts : List (List Char)) :
    parseCover (fuel + 1) ("F" :: String.ofList c :: String.ofList tau :: String.ofList nl ::
      ts.map String.ofList) = (parseLeafL c tau nl ts).map mapRest := by
  rw [parseCover.eq_3]
  simp only [parseLeafL, parseRat_ofList, parseNat_ofList, parsePanels_map]
  rcases parseRatL c with _ | cq <;> rcases parseRatL tau with _ | tq <;>
    rcases parseNatL nl with _ | kl <;> simp only [Option.map_none]
  rcases parsePanelsL kl ts with _ | ⟨low, _ | ⟨nh, ts1⟩⟩ <;>
    simp only [Option.map_none, Option.map_some, mapRest_mk, List.map_nil, List.map_cons,
      parseNat_ofList, parsePanels_map]
  rcases parseNatL nh with _ | kh <;> simp only [Option.map_none]
  rcases parsePanelsL kh ts1 with _ | ⟨high, _ | ⟨nn, ts2⟩⟩ <;>
    simp only [Option.map_none, Option.map_some, mapRest_mk, List.map_nil, List.map_cons,
      parseNat_ofList, parseEnds_map]
  rcases parseNatL nn with _ | kn <;> simp only [Option.map_none]
  rcases parseEndsL kn ts2 with _ | ⟨normal, ts3⟩ <;>
    simp only [Option.map_none, Option.map_some, mapRest_mk]

theorem parseCover_map : ∀ (fuel : Nat) (ts : List (List Char)),
    parseCover fuel (ts.map String.ofList) = (parseCoverL fuel ts).map mapRest
  | 0, ts => by rw [parseCover.eq_1]; rfl
  | fuel + 1, [] => by
    rw [List.map_nil, parseCover.eq_4]
    · rfl
    · simp
    · intro _ _ _ _ _ h; cases h
    · intro _ _ _ _ _ _ h; cases h
  | fuel + 1, t :: ts => by
    by_cases hS : t = ['S']
    · subst hS
      rcases ts with _ | ⟨axis, _ | ⟨m, ts⟩⟩
      · rw [List.map_cons, List.map_nil, ofList_S, parseCover.eq_4]
        · rfl
        · simp
        · intro _ _ _ _ _ h; injection h with _ h; cases h
        · intro _ _ _ _ _ _ h; injection h with h; exact absurd h (by decide)
      · rw [List.map_cons, List.map_cons, List.map_nil, ofList_S, parseCover.eq_4]
        · rfl
        · simp
        · intro _ _ _ _ _ h; injection h with _ h; cases h
        · intro _ _ _ _ _ _ h; injection h with h; exact absurd h (by decide)
      · rw [List.map_cons, List.map_cons, List.map_cons, ofList_S, parseCover.eq_2]
        simp only [parseCoverL, ite_true, parseRat_ofList, parseCover_map fuel ts]
        rcases parseRatL m with _ | mq <;> rcases parseCoverL fuel ts with _ | ⟨left, ts'⟩ <;>
          try rfl
        simp only [Option.map_some, mapRest_mk, parseCover_map fuel ts']
        rcases parseCoverL fuel ts' with _ | ⟨right, ts''⟩
        · rfl
        · simp only [Option.map_some, mapRest_mk, ofList_beq_one]
    · by_cases hF : t = ['F']
      · subst hF
        rcases ts with _ | ⟨c, _ | ⟨tau, _ | ⟨nl, ts⟩⟩⟩
        · rw [List.map_cons, List.map_nil, ofList_F, parseCover.eq_4]
          · rfl
          · simp
          · intro _ _ _ _ _ h; injection h with h; exact absurd h (by decide)
          · intro _ _ _ _ _ _ h; injection h with _ h; cases h
        · rw [List.map_cons, List.map_cons, List.map_nil, ofList_F, parseCover.eq_4]
          · rfl
          · simp
          · intro _ _ _ _ _ h; injection h with h; exact absurd h (by decide)
          · intro _ _ _ _ _ _ h; injection h with _ h; injection h with _ h; cases h
        · rw [List.map_cons, List.map_cons, List.map_cons, List.map_nil, ofList_F,
            parseCover.eq_4]
          · rfl
          · simp
          · intro _ _ _ _ _ h; injection h with h; exact absurd h (by decide)
          · intro _ _ _ _ _ _ h
            injection h with _ h; injection h with _ h; injection h with _ h; cases h
        · rw [List.map_cons, List.map_cons, List.map_cons, List.map_cons, ofList_F, leaf_map]
          simp only [parseCoverL, show (['F'] : List Char) ≠ ['S'] by decide, ite_false, ite_true]
      · rw [List.map_cons, parseCover.eq_4]
        · simp only [parseCoverL, hS, hF, ite_false, Option.map_none]
        · simp
        · intro _ _ _ _ _ h; injection h with h; exact hS ((ofList_eq_S_iff t).1 h)
        · intro _ _ _ _ _ _ h; injection h with h; exact hF ((ofList_eq_F_iff t).1 h)

/-! ### Main theorems -/

theorem coverStringAccepted_eq (n : Nat) (s : String) :
    coverStringAccepted n s = coverListAccepted n s.toList := by
  unfold coverStringAccepted coverListAccepted
  rw [tokens_eq, parseCover_map]
  rcases parseCoverL 64 (tokensL s.toList) with _ | ⟨cov, _ | ⟨t, rest⟩⟩ <;> rfl

theorem coverStringAcceptedBE_eq (n : Nat) (blo bhi : Rat) (s : String) :
    coverStringAcceptedBE n blo bhi s = coverListAcceptedBE n blo bhi s.toList := by
  unfold coverStringAcceptedBE coverListAcceptedBE
  rw [tokens_eq, parseCover_map]
  rcases parseCoverL 64 (tokensL s.toList) with _ | ⟨cov, _ | ⟨t, rest⟩⟩ <;> rfl

theorem coverStringAcceptedDW_eq (n : Nat) (dlo dhi : Rat) (s : String) :
    coverStringAcceptedDW n dlo dhi s = coverListAcceptedDW n dlo dhi s.toList := by
  unfold coverStringAcceptedDW coverListAcceptedDW
  rw [tokens_eq, parseCover_map]
  rcases parseCoverL 64 (tokensL s.toList) with _ | ⟨cov, _ | ⟨t, rest⟩⟩ <;> rfl

end NativeTrust.BE

#print axioms NativeTrust.BE.coverStringAccepted_eq
#print axioms NativeTrust.BE.coverStringAcceptedBE_eq
#print axioms NativeTrust.BE.coverStringAcceptedDW_eq
