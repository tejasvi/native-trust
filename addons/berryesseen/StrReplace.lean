/-!
`String.replace` with a one-character `String` pattern, as a map on `toList`.
Core only (Lean `v4.34.0-rc2`, no imports beyond the `Init` prelude).

Proof idea: `String.replace` is `Slice.replace`, a fold over the search steps of the string
searcher; turn the fold into `List.foldl` over the searcher's `toList` (`Std.Iter.foldl_toList`) and
induct on the core correctness predicate `IsValidSearchFrom` provided by
`ForwardStringSearcher.lawfulToForwardSearcherModel`.
-/

namespace NativeTrust.StrFast

open String String.Slice.Pattern String.Slice.Pattern.Model

theorem flatMap_eq_self_of_not_mem {c : Char} {r : List Char} :
    ∀ {L : List Char}, c ∉ L → L.flatMap (fun d => if d = c then r else [d]) = L
  | [], _ => rfl
  | d :: L, h => by
    have hd : d ≠ c := by rintro rfl; simp at h
    have hL : c ∉ L := fun hc => h (List.mem_cons_of_mem _ hc)
    rw [List.flatMap_cons, ite_eq_right hd, flatMap_eq_self_of_not_mem hL]
    rfl

theorem flatMap_ite_singleton (c c' : Char) : ∀ L : List Char,
    L.flatMap (fun d => if d = c then [c'] else [d]) = L.map (fun d => if d = c then c' else d)
  | [] => rfl
  | d :: L => by
    rw [List.flatMap_cons, List.map_cons, flatMap_ite_singleton c c' L]
    by_cases h : d = c <;> simp [h]

/-- Invariant of the `Slice.replace` fold for a pattern `pat` with `pat.toList = [c]`, for any step
function `f` that behaves like the one in `Slice.replace`. -/
theorem foldl_replace_aux {pat : String} {c : Char} (hpat : pat.toList = [c]) (r : String)
    {t : Slice} (f : String → SearchStep t → String)
    (hm : ∀ acc a b, (f acc (.matched a b)).toList = acc.toList ++ r.toList)
    (hr : ∀ acc a b, (f acc (.rejected a b)).toList = acc.toList ++ (t.slice! a b).copy.toList)
    {pos : t.Pos} {l : List (SearchStep t)} (hv : IsValidSearchFrom pat pos l) :
    ∀ acc : String, (l.foldl f acc).toList =
      acc.toList ++ (t.sliceFrom pos).copy.toList.flatMap (fun d => if d = c then r.toList else [d]) := by
  induction hv with
  | endPos =>
    intro acc
    rw [(Slice.splits_endPos t).copy_sliceFrom_eq]
    simp
  | matched hlm hv' ih =>
    intro acc
    obtain ⟨t₁, t₂, h1, h2⟩ := ForwardStringSearcher.isLongestMatchAt_iff_splits.1 hlm
    rw [List.foldl_cons, ih, hm, h1.copy_sliceFrom_eq, h2.copy_sliceFrom_eq, String.toList_append, hpat]
    simp
  | mismatched hlt hno hv' ih =>
    intro acc
    have hle := Std.le_of_lt hlt
    obtain ⟨t₁, t₂, h1, h2⟩ := Slice.copy_slice_eq_iff_splits.1 ⟨hle, rfl⟩
    have hnc : c ∉ (t.slice _ _ hle).copy.toList := by
      generalize hmdef : (t.slice _ _ hle).copy = m at h1 h2
      intro hc
      obtain ⟨u, v, huv⟩ := List.append_of_mem hc
      have heq : t.copy = (t₁ ++ String.ofList u) ++ (pat ++ (String.ofList v ++ t₂)) := by
        rw [h1.eq_append]
        apply String.ext
        simp [String.toList_append, huv, hpat]
      have hp := Slice.Pos.splits_ofEqAppend heq
      refine hno (Slice.Pos.ofEqAppend heq) ?_ ?_ (ForwardStringSearcher.matchesAt_iff_splits.2 ⟨_, _, hp⟩)
      · refine (h1.le_iff_exists_eq_append hp).2 ⟨String.ofList u, rfl, ?_⟩
        apply String.ext
        simp [String.toList_append, huv, hpat]
      · refine (hp.lt_iff_exists_eq_append h2).2 ⟨pat ++ String.ofList v, ?_, ?_, ?_⟩
        · intro h
          have := congrArg String.toList h
          simp [String.toList_append, hpat] at this
        · apply String.ext
          simp [String.toList_append, huv, hpat]
        · apply String.ext
          simp [String.toList_append, hpat]
    rw [List.foldl_cons, ih, hr, h1.copy_sliceFrom_eq, h2.copy_sliceFrom_eq, String.toList_append,
      Slice.slice!, dite_eq_left hle, List.flatMap_append, flatMap_eq_self_of_not_mem hnc, List.append_assoc]

/-- General version: one-character pattern `String.singleton c`, any replacement string `r`. -/
theorem toList_replace_singleton (s : String) (c : Char) (r : String) :
    (s.replace (String.singleton c) r).toList =
      s.toList.flatMap (fun d => if d = c then r.toList else [d]) := by
  have hpat : (String.singleton c).toList = [c] := String.toList_singleton c
  have hne : String.singleton c ≠ "" := by
    intro h
    have := congrArg String.toList h
    simp at this
  have hv := (ForwardStringSearcher.lawfulToForwardSearcherModel hne).isValidSearchFrom_toList s.toSlice
  unfold String.replace String.Slice.replace
  rw [← Std.Iter.foldl_toList]
  refine (foldl_replace_aux hpat r _ ?_ ?_ hv "").trans ?_
  · intro acc a b
    show (acc ++ (r.toSlice).copy).toList = acc.toList ++ r.toList
    rw [String.toList_append, String.copy_toSlice]
  · intro acc a b
    show (acc ++ (s.toSlice.slice! a b).copy).toList = _
    rw [String.toList_append]
  · rw [(Slice.splits_startPos s.toSlice).copy_sliceFrom_eq, String.copy_toSlice]
    simp

end NativeTrust.StrFast

/-- The needed lemma; stated at top level with no `open`, so `s.replace "\n" " "` elaborates
exactly as in user code. -/
theorem NativeTrust.StrFast.toList_replace_newline (s : String) :
    (s.replace "\n" " ").toList = s.toList.map (fun c => if c = '\n' then ' ' else c) := by
  have h := NativeTrust.StrFast.toList_replace_singleton s '\n' " "
  have hlit : String.singleton '\n' = "\n" := by decide
  have hsp : (" " : String).toList = [' '] := by decide
  rw [hlit, hsp] at h
  rw [h]
  exact NativeTrust.StrFast.flatMap_ite_singleton '\n' ' ' s.toList

-- usage check: rewriting a user-style term
example (s : String) :
    s.replace "\n" " " = String.ofList (s.toList.map (fun c => if c = '\n' then ' ' else c)) := by
  rw [← NativeTrust.StrFast.toList_replace_newline, String.ofList_toList]

#print axioms NativeTrust.StrFast.toList_replace_newline
#print axioms NativeTrust.StrFast.toList_replace_singleton
