import NativeTrust.Copy
import NativeTrust.StrFast

/-!
# List-level kernel forms of iterator-based `String` functions

Since Lean 4.2x many `String` functions run on `String.Slice` iterators: `Std.Iter` loops on
`WellFounded.extrinsicFix` (a classical well-foundedness test) with iterator states in `Std.Shrink`
(defined with the opaque `Std.Internal.idOpaque`), so the kernel cannot evaluate them, whatever the
input. This module gives proved list-level versions, registered with `@[kernel_replace_retry]` (and
`@[kernel_fold]` for the pattern-generic `replace` and `contains`): when every default route fails,
NativeTrust retries once with them, evaluates the list versions and bridges back by congruence. They are
not used before that retry, because copying everything that reaches a `String` function can cost more
than a plain evaluation that already works. The list versions read characters with
`NativeTrust.toListFast` (linear decoding) instead of `String.toList`.
-/

-- many proofs: async elaboration reserves a thread stack per theorem ("failed to create thread" under
-- `ulimit -v`)
set_option Elab.async false

namespace NativeTrust.StrLib

universe u

/-- `String.Slice.foldl` over the slice's characters. -/
def sliceFoldl {α : Type u} (f : α → Char → α) (init : α) (s : String.Slice) : α :=
  (toListFast s.copy).foldl f init

@[kernel_replace_retry] theorem sliceFoldl_eq : @String.Slice.foldl.{u} = @sliceFoldl.{u} := by
  funext α f init s
  rw [sliceFoldl, toListFast_eq]
  exact String.Slice.foldl_eq_foldl_toList

/-- `String.Slice.foldr` over the slice's characters. -/
def sliceFoldr {α : Type u} (f : Char → α → α) (init : α) (s : String.Slice) : α :=
  (toListFast s.copy).foldr f init

@[kernel_replace_retry] theorem sliceFoldr_eq : @String.Slice.foldr.{u} = @sliceFoldr.{u} := by
  funext α f init s
  rw [sliceFoldr, toListFast_eq]
  exact String.Slice.foldr_eq_foldr_toList

set_option backward.do.legacy false in
/-- The loop of `String.Slice.isNat`, verbatim, over a character list (core is compiled with the new
`do` elaborator, the default only from Lean 4.34 on). -/
def isNatList (l : List Char) : Bool := Id.run do
  let mut lastWasDigit := false

  for c in l do
    if c = '_' then
      if !lastWasDigit then
        return false
      lastWasDigit := false
    else if c.isDigit then
      lastWasDigit := true
    else
      return false

  return lastWasDigit

/-- `String.Slice.isNat` over the slice's characters. -/
def sliceIsNat (s : String.Slice) : Bool :=
  isNatList (toListFast s.copy)

@[kernel_replace_retry] theorem sliceIsNat_eq : @String.Slice.isNat = @sliceIsNat := by
  funext s
  rw [sliceIsNat, toListFast_eq]
  simp only [String.Slice.isNat, isNatList, String.Slice.forIn_eq_forIn_toList]

/-! ## `String.replace` and `String.Slice.replace` with a `String` pattern

These functions take the pattern's searcher as type-class arguments, so they are replaced for the
`String` pattern instance only: `@[kernel_fold]` folds their occurrences with a `String` pattern into
`replaceStrPat`/`sliceReplaceStrPat`, which `@[kernel_replace_retry]` maps to list-level versions. -/

section Replace
open String String.Slice.Pattern String.Slice.Pattern.Model

/-- Replacement of a nonempty pattern `pat` by `r` on character lists, left to right, without
overlaps; `k` characters of the last match are still to be skipped. Structural recursion. -/
def replGo (pat r : List Char) : Nat → List Char → List Char
  | _, [] => []
  | 0, c :: cs => if pat.isPrefixOf (c :: cs) then r ++ replGo pat r (pat.length - 1) cs
                  else c :: replGo pat r 0 cs
  | k + 1, _ :: cs => replGo pat r k cs

theorem replGo_skip (pat r : List Char) : ∀ (u rest : List Char),
    replGo pat r u.length (u ++ rest) = replGo pat r 0 rest
  | [], _ => rfl
  | _ :: u, rest => by
    rw [List.length_cons, List.cons_append, replGo, replGo_skip pat r u rest]

theorem replGo_match {pat r : List Char} (hp : pat ≠ []) (rest : List Char) :
    replGo pat r 0 (pat ++ rest) = r ++ replGo pat r 0 rest := by
  match pat, hp with
  | c :: u, _ =>
    have hpre : (c :: u).isPrefixOf (c :: (u ++ rest)) = true := by
      rw [List.isPrefixOf_iff_prefix]; exact ⟨rest, rfl⟩
    rw [List.cons_append, replGo, if_pos hpre, List.length_cons, Nat.add_sub_cancel, replGo_skip]

theorem replGo_nomatch {pat r : List Char} {c : Char} {cs : List Char} (h : ¬ pat <+: c :: cs) :
    replGo pat r 0 (c :: cs) = c :: replGo pat r 0 cs := by
  rw [replGo, if_neg (by rwa [List.isPrefixOf_iff_prefix])]

theorem replGo_region {pat r : List Char} : ∀ (m rest : List Char),
    (∀ u v, m = u ++ v → v ≠ [] → ¬ pat <+: v ++ rest) →
    replGo pat r 0 (m ++ rest) = m ++ replGo pat r 0 rest
  | [], _, _ => rfl
  | d :: m, rest, h => by
    have h0 : ¬ pat <+: d :: (m ++ rest) := h [] (d :: m) rfl (List.cons_ne_nil _ _)
    rw [List.cons_append, replGo_nomatch h0,
      replGo_region m rest (fun u v huv hv => h (d :: u) v (by rw [huv, List.cons_append]) hv),
      List.cons_append]

/-- The position between `t₁` and `t₂` of a slice whose copy is `t₁ ++ t₂` (core's
`Slice.Pos.ofEqAppend`, which Lean 4.30 lacks). -/
def posOfEqAppend {s : Slice} {t₁ t₂ : String} (h : s.copy = t₁ ++ t₂) : s.Pos :=
  s.pos t₁.rawEndPos
    (by simpa [← Pos.Raw.isValid_copy_iff, h] using ((Pos.Raw.isValid_rawEndPos).append_right t₂))

theorem splits_posOfEqAppend {s : Slice} {t₁ t₂ : String} (h : s.copy = t₁ ++ t₂) :
    (posOfEqAppend h).Splits t₁ t₂ where
  eq_append := h
  offset_eq_rawEndPos := by simp [posOfEqAppend]

theorem foldl_replace_aux {pat : String} (hpat : pat ≠ "") (r : String)
    {t : Slice} (f : String → SearchStep t → String)
    (hm : ∀ acc a b, (f acc (.matched a b)).toList = acc.toList ++ r.toList)
    (hr : ∀ acc a b, (f acc (.rejected a b)).toList = acc.toList ++ (t.slice! a b).copy.toList)
    {pos : t.Pos} {l : List (SearchStep t)} (hv : IsValidSearchFrom pat pos l) :
    ∀ acc : String, (l.foldl f acc).toList =
      acc.toList ++ replGo pat.toList r.toList 0 (t.sliceFrom pos).copy.toList := by
  have hpne : pat.toList ≠ [] := by
    intro h; apply hpat; apply String.ext; rw [h, String.toList_empty]
  induction hv with
  | endPos =>
    intro acc
    rw [(Slice.splits_endPos t).copy_sliceFrom_eq]
    simp [replGo]
  | matched hlm hv' ih =>
    intro acc
    -- Lean 4.30 states `isLongestMatchAt_iff_splits` under `pat ≠ ""`
    obtain ⟨t₁, t₂, h1, h2⟩ : ∃ t₁ t₂, Slice.Pos.Splits _ t₁ (pat ++ t₂) ∧ Slice.Pos.Splits _ (t₁ ++ pat) t₂ := by
      first
        | exact (ForwardStringSearcher.isLongestMatchAt_iff_splits hpat).1 hlm
        | exact ForwardStringSearcher.isLongestMatchAt_iff_splits.1 hlm
    rw [List.foldl_cons, ih, hm, h1.copy_sliceFrom_eq, h2.copy_sliceFrom_eq, String.toList_append,
      replGo_match hpne]
    simp
  | mismatched hlt hno hv' ih =>
    intro acc
    have hle := Std.le_of_lt hlt
    obtain ⟨t₁, t₂, h1, h2⟩ := Slice.copy_slice_eq_iff_splits.1 ⟨hle, rfl⟩
    generalize hmdef : (t.slice _ _ hle).copy = m at h1 h2
    have hreg : ∀ u v, m.toList = u ++ v → v ≠ [] → ¬ pat.toList <+: v ++ t₂.toList := by
      rintro u v huv hv ⟨w, hw⟩
      have heq : t.copy = (t₁ ++ String.ofList u) ++ (pat ++ String.ofList w) := by
        rw [h1.eq_append]
        apply String.ext
        simp only [String.toList_append, String.toList_ofList, huv, List.append_assoc]
        rw [hw]
      have hp := splits_posOfEqAppend heq
      have hma : MatchesAt pat (posOfEqAppend heq) := by
        first
          | exact (ForwardStringSearcher.matchesAt_iff_splits hpat).2 ⟨_, _, hp⟩
          | exact ForwardStringSearcher.matchesAt_iff_splits.2 ⟨_, _, hp⟩
      refine hno (posOfEqAppend heq) ?_ ?_ hma
      · refine (h1.le_iff_exists_eq_append hp).2 ⟨String.ofList u, rfl, ?_⟩
        apply String.ext
        simp only [String.toList_append, String.toList_ofList, huv, List.append_assoc]
        rw [hw]
      · refine (hp.lt_iff_exists_eq_append h2).2 ⟨String.ofList v, ?_, ?_, ?_⟩
        · intro h
          have := congrArg String.toList h
          rw [String.toList_ofList, String.toList_empty] at this
          exact hv this
        · apply String.ext
          simp [String.toList_append, huv]
        · apply String.ext
          simp only [String.toList_append, String.toList_ofList]
          rw [hw]
    rw [List.foldl_cons, ih, hr, h1.copy_sliceFrom_eq, h2.copy_sliceFrom_eq, String.toList_append,
      Slice.slice!, dif_pos hle, hmdef, replGo_region _ _ hreg, List.append_assoc]

theorem toList_sliceReplace_ne (t : Slice) (pat r : String) (hpat : pat ≠ "") :
    (t.replace pat r).toList = replGo pat.toList r.toList 0 t.copy.toList := by
  have hv := (ForwardStringSearcher.lawfulToForwardSearcherModel hpat).isValidSearchFrom_toList t
  unfold String.Slice.replace
  rw [← Std.Iter.foldl_toList]
  refine (foldl_replace_aux hpat r _ ?_ ?_ hv "").trans ?_
  · intro acc a b
    show (acc ++ (r.toSlice).copy).toList = acc.toList ++ r.toList
    rw [String.toList_append, String.copy_toSlice]
  · intro acc a b
    show (acc ++ (t.slice! a b).copy).toList = _
    rw [String.toList_append]
  · rw [(Slice.splits_startPos t).copy_sliceFrom_eq]
    simp

theorem toList_replace_ne (s pat r : String) (hpat : pat ≠ "") :
    (s.replace pat r).toList = replGo pat.toList r.toList 0 s.toList := by
  have h := toList_sliceReplace_ne s.toSlice pat r hpat
  rw [String.copy_toSlice] at h
  exact h


/-- Replacement of the empty pattern on character lists: `r` before every character and at the end
(`"abc".replace "" "k" = "kakbkck"`). -/
def replEmpty (r : List Char) : List Char → List Char
  | [] => r
  | c :: cs => r ++ c :: replEmpty r cs

theorem foldl_replace_empty_aux (r : String) {t : Slice} (f : String → SearchStep t → String)
    (hm : ∀ acc a b, (f acc (.matched a b)).toList = acc.toList ++ r.toList)
    (hr : ∀ acc a b, (f acc (.rejected a b)).toList = acc.toList ++ (t.slice! a b).copy.toList) :
    ∀ (L : List Char) (pos : t.Pos) (acc : String), (t.sliceFrom pos).copy.toList = L →
      ((Std.Iter.mk (.emptyBefore pos : ForwardSliceSearcher t)).toList.foldl f acc).toList =
        acc.toList ++ replEmpty r.toList L := by
  intro L
  induction L with
  | nil =>
    intro pos acc hL
    have h : pos = t.endPos := by
      apply Classical.byContradiction
      intro h
      rw [(Slice.Pos.splits_next_right pos h).copy_sliceFrom_eq, String.toList_append,
        String.toList_singleton] at hL
      exact List.cons_ne_nil _ _ hL
    subst h
    rw [ForwardSliceSearcher.toList_emptyBefore_eq, dif_pos rfl, List.foldl_cons, List.foldl_nil, hm]
    rfl
  | cons c L ih =>
    intro pos acc hL
    have h : pos ≠ t.endPos := by
      intro h
      subst h
      rw [(Slice.splits_endPos t).copy_sliceFrom_eq, String.toList_empty] at hL
      exact List.cons_ne_nil _ _ hL.symm
    have h1 := Slice.Pos.splits_next_right pos h
    have h2 := Slice.Pos.splits_next pos h
    obtain ⟨hle, hcopy⟩ := Slice.copy_slice_eq_iff_splits.2 ⟨_, _, h1, h2⟩
    rw [h1.copy_sliceFrom_eq, String.toList_append, String.toList_singleton, List.singleton_append] at hL
    obtain ⟨hc, hL'⟩ := List.cons.inj hL
    subst hc
    rw [ForwardSliceSearcher.toList_emptyBefore_eq, dif_neg h, ForwardSliceSearcher.toList_emptyAt_eq,
      List.foldl_cons, List.foldl_cons, ih (pos.next h) _ hL', hr, hm, Slice.slice!, dif_pos hle, hcopy,
      String.toList_singleton]
    simp [replEmpty, List.append_assoc]

theorem toList_sliceReplace_empty (t : Slice) (r : String) :
    (t.replace "" r).toList = replEmpty r.toList t.copy.toList := by
  unfold String.Slice.replace
  rw [ForwardStringSearcher.toSearcher_empty, ← Std.Iter.foldl_toList]
  refine (foldl_replace_empty_aux r _ ?_ ?_ t.copy.toList t.startPos "" ?_).trans ?_
  · intro acc a b
    show (acc ++ (r.toSlice).copy).toList = acc.toList ++ r.toList
    rw [String.toList_append, String.copy_toSlice]
  · intro acc a b
    show (acc ++ (t.slice! a b).copy).toList = _
    rw [String.toList_append]
  · rw [(Slice.splits_startPos t).copy_sliceFrom_eq]
  · simp

theorem eq_empty_of_toListFast_eq_nil {pat : String} (h : toListFast pat = []) : pat = "" := by
  apply String.ext
  rw [← toListFast_eq, h, String.toList_empty]

theorem ne_empty_of_toListFast_eq_cons {pat : String} {p : Char} {ps : List Char}
    (h : toListFast pat = p :: ps) : pat ≠ "" := by
  rintro rfl
  rw [toListFast_eq, String.toList_empty] at h
  exact List.cons_ne_nil _ _ h.symm

/-- `String.replace` with a `String` pattern (the occurrences that `@[kernel_fold]` folds). -/
@[kernel_fold] def replaceStrPat (s pat r : String) : String := s.replace pat r

/-- `String.replace` with a `String` pattern on character lists. -/
def replaceStr (s pat r : String) : String :=
  match toListFast pat with
  | [] => ofListFast (replEmpty (toListFast r) (toListFast s))
  | p :: ps => ofListFast (replGo (p :: ps) (toListFast r) 0 (toListFast s))

@[kernel_replace_retry] theorem replaceStrPat_eq : @replaceStrPat = @replaceStr := by
  funext s pat r
  unfold replaceStrPat replaceStr
  split
  · rename_i h
    have hpat := eq_empty_of_toListFast_eq_nil h
    subst hpat
    apply String.ext
    have h' := toList_sliceReplace_empty s.toSlice r
    rw [String.copy_toSlice] at h'
    rw [← ofList_eq_ofListFast, String.toList_ofList, toListFast_eq, toListFast_eq]
    exact h'
  · rename_i p ps h
    apply String.ext
    rw [← ofList_eq_ofListFast, String.toList_ofList, toList_replace_ne s pat r
      (ne_empty_of_toListFast_eq_cons h), ← h, toListFast_eq, toListFast_eq, toListFast_eq]

/-- `String.Slice.replace` with a `String` pattern (the occurrences that `@[kernel_fold]` folds). -/
@[kernel_fold] def sliceReplaceStrPat (s : String.Slice) (pat r : String) : String := s.replace pat r

/-- `String.Slice.replace` with a `String` pattern on character lists. -/
def sliceReplaceStr (s : String.Slice) (pat r : String) : String :=
  match toListFast pat with
  | [] => ofListFast (replEmpty (toListFast r) (toListFast s.copy))
  | p :: ps => ofListFast (replGo (p :: ps) (toListFast r) 0 (toListFast s.copy))

@[kernel_replace_retry] theorem sliceReplaceStrPat_eq : @sliceReplaceStrPat = @sliceReplaceStr := by
  funext s pat r
  unfold sliceReplaceStrPat sliceReplaceStr
  split
  · rename_i h
    have hpat := eq_empty_of_toListFast_eq_nil h
    subst hpat
    apply String.ext
    rw [← ofList_eq_ofListFast, String.toList_ofList, toListFast_eq, toListFast_eq]
    exact toList_sliceReplace_empty s r
  · rename_i p ps h
    apply String.ext
    rw [← ofList_eq_ofListFast, String.toList_ofList, toList_sliceReplace_ne s pat r
      (ne_empty_of_toListFast_eq_cons h), ← h, toListFast_eq, toListFast_eq, toListFast_eq]

end Replace

/-! ## `String.contains` and `String.Slice.contains` with a `Char` or `String` pattern

Folded per pattern type, like `replace`. The equations come from core's `contains_char_eq` (Lean ≥ 4.31;
on 4.30 from `contains_char_eq_contains_beq` and `contains_bool_eq`) and `contains_string_iff`. -/

section Contains
open String

theorem contains_char_toList (s : String) (c : Char) : s.contains c = decide (c ∈ s.toList) := by
  first
    | exact String.contains_char_eq
    | (show s.toSlice.contains c = _
       rw [String.Slice.contains_char_eq_contains_beq, String.Slice.contains_bool_eq, String.copy_toSlice]
       simp)

theorem sliceContains_char_toList (s : Slice) (c : Char) : s.contains c = decide (c ∈ s.copy.toList) := by
  first
    | exact String.Slice.contains_char_eq
    | (rw [String.Slice.contains_char_eq_contains_beq, String.Slice.contains_bool_eq]
       simp)

theorem contains_string_toList (s t : String) : s.contains t = decide (t.toList <:+: s.toList) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact String.contains_string_iff

theorem sliceContains_string_toList (s : Slice) (t : String) :
    s.contains t = decide (t.toList <:+: s.copy.toList) := by
  rw [Bool.eq_iff_iff, decide_eq_true_iff]
  exact String.Slice.contains_string_iff

/-- `String.contains` with a `Char` pattern (the occurrences that `@[kernel_fold]` folds). -/
@[kernel_fold] def containsCharPat (s : String) (c : Char) : Bool := s.contains c

def containsChar (s : String) (c : Char) : Bool := decide (c ∈ toListFast s)

@[kernel_replace_retry] theorem containsCharPat_eq : @containsCharPat = @containsChar := by
  funext s c
  rw [containsCharPat, containsChar, toListFast_eq]
  exact contains_char_toList s c

/-- `String.Slice.contains` with a `Char` pattern. -/
@[kernel_fold] def sliceContainsCharPat (s : String.Slice) (c : Char) : Bool := s.contains c

def sliceContainsChar (s : String.Slice) (c : Char) : Bool := decide (c ∈ toListFast s.copy)

@[kernel_replace_retry] theorem sliceContainsCharPat_eq : @sliceContainsCharPat = @sliceContainsChar := by
  funext s c
  rw [sliceContainsCharPat, sliceContainsChar, toListFast_eq]
  exact sliceContains_char_toList s c

/-- `String.contains` with a `String` pattern. -/
@[kernel_fold] def containsStrPat (s t : String) : Bool := s.contains t

def containsStr (s t : String) : Bool := decide (toListFast t <:+: toListFast s)

@[kernel_replace_retry] theorem containsStrPat_eq : @containsStrPat = @containsStr := by
  funext s t
  rw [containsStrPat, containsStr, toListFast_eq, toListFast_eq]
  exact contains_string_toList s t

/-- `String.Slice.contains` with a `String` pattern. -/
@[kernel_fold] def sliceContainsStrPat (s : String.Slice) (t : String) : Bool := s.contains t

def sliceContainsStr (s : String.Slice) (t : String) : Bool := decide (toListFast t <:+: toListFast s.copy)

@[kernel_replace_retry] theorem sliceContainsStrPat_eq : @sliceContainsStrPat = @sliceContainsStr := by
  funext s t
  rw [sliceContainsStrPat, sliceContainsStr, toListFast_eq, toListFast_eq]
  exact sliceContains_string_toList s t

end Contains

end NativeTrust.StrLib
