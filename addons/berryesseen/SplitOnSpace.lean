/-!
# Legacy `String.splitOn` on a one-character separator equals `List.splitOn` on `toList`

Core-only (Lean v4.34.0-rc2, no imports beyond the `Init` prelude). Main results:
* `NativeTrust.StrFast.splitOn_singleton` (any `c : Char`, multi-byte included)
* `NativeTrust.StrFast.splitOn_space`, `NativeTrust.StrFast.splitOn_slash`
Helpers live in `NativeTrust.StrFast.SplitOnProof`.
-/

namespace NativeTrust.StrFast

namespace SplitOnProof

/-- UTF-8 byte length of a list of characters. -/
def bl : List Char → Nat
  | [] => 0
  | c :: l => c.utf8Size + bl l

@[simp] theorem bl_nil : bl [] = 0 := rfl
@[simp] theorem bl_cons (c : Char) (l : List Char) : bl (c :: l) = c.utf8Size + bl l := rfl

theorem bl_append (a b : List Char) : bl (a ++ b) = bl a + bl b := by
  induction a with
  | nil => simp
  | cons c a ih => simp [ih, Nat.add_assoc]

theorem bl_singleton (c : Char) : bl [c] = c.utf8Size := by simp

theorem bl_pos_of_ne_nil {l : List Char} (h : l ≠ []) : 0 < bl l := by
  cases l with
  | nil => exact absurd rfl h
  | cons c l =>
    have := Char.utf8Size_pos c
    rw [bl_cons]; omega

theorem bl_eq_zero_iff (l : List Char) : bl l = 0 ↔ l = [] := by
  constructor
  · intro h
    cases l with
    | nil => rfl
    | cons c l =>
      have := Char.utf8Size_pos c
      rw [bl_cons] at h; omega
  · intro h; subst h; rfl

theorem size_utf8Encode (l : List Char) : l.utf8Encode.size = bl l := by
  induction l with
  | nil => simp [ByteArray.size_empty]
  | cons c l ih =>
    rw [List.utf8Encode_cons, ByteArray.size_append, ih, List.utf8Encode_singleton,
      List.size_toByteArray, String.length_utf8EncodeChar, bl_cons]

theorem utf8ByteSize_eq (s : String) : s.utf8ByteSize = bl s.toList := by
  rw [← String.size_toByteArray, ← String.utf8Encode_toList, size_utf8Encode]

theorem utf8GetAux_append (p : List Char) (x : Char) (t : List Char) :
    ∀ (i q : String.Pos.Raw), q.byteIdx = i.byteIdx + bl p →
      String.Pos.Raw.utf8GetAux (p ++ x :: t) i q = x := by
  induction p with
  | nil =>
    intro i q hq
    have hiq : i = q := String.Pos.Raw.ext (by rw [bl_nil, Nat.add_zero] at hq; omega)
    rw [List.nil_append, String.Pos.Raw.utf8GetAux, ite_eq_left hiq]
  | cons y p ih =>
    intro i q hq
    have hiq : i ≠ q := by
      intro h
      rw [h, bl_cons] at hq
      have := Char.utf8Size_pos y
      omega
    rw [List.cons_append, String.Pos.Raw.utf8GetAux, ite_eq_right hiq]
    apply ih
    rw [String.Pos.Raw.byteIdx_add_char, hq, bl_cons]
    omega

theorem get_of_eq (s : String) (p : List Char) (x : Char) (t : List Char)
    (hs : s.toList = p ++ x :: t) (i : String.Pos.Raw) (hi : i.byteIdx = bl p) :
    String.Pos.Raw.get s i = x := by
  show String.Pos.Raw.utf8GetAux s.toList 0 i = x
  rw [hs]
  exact utf8GetAux_append p x t 0 i (by rw [hi, String.Pos.Raw.byteIdx_zero, Nat.zero_add])

theorem next_of_eq (s : String) (p : List Char) (x : Char) (t : List Char)
    (hs : s.toList = p ++ x :: t) (i : String.Pos.Raw) (hi : i.byteIdx = bl p) :
    (String.Pos.Raw.next s i).byteIdx = bl p + x.utf8Size := by
  show (i + String.Pos.Raw.get s i).byteIdx = _
  rw [get_of_eq s p x t hs i hi, String.Pos.Raw.byteIdx_add_char, hi]

theorem atEnd_of_eq (s : String) (p t : List Char) (hs : s.toList = p ++ t)
    (i : String.Pos.Raw) (hi : i.byteIdx = bl p) :
    String.Pos.Raw.atEnd s i = true ↔ t = [] := by
  have hsz : s.utf8ByteSize = bl p + bl t := by rw [utf8ByteSize_eq, hs, bl_append]
  show decide (i.byteIdx ≥ s.utf8ByteSize) = true ↔ t = []
  rw [decide_eq_true_eq, hsz, hi, ← bl_eq_zero_iff]
  constructor
  · intro h; omega
  · intro h; omega

theorem go₂_append (m t : List Char) :
    ∀ (i e : String.Pos.Raw), e.byteIdx = i.byteIdx + bl m →
      String.Pos.Raw.extract.go₂ (m ++ t) i e = m := by
  induction m with
  | nil =>
    intro i e he
    have hie : i = e := String.Pos.Raw.ext (by rw [bl_nil, Nat.add_zero] at he; omega)
    cases t with
    | nil => rw [List.nil_append, String.Pos.Raw.extract.go₂]
    | cons y t => rw [List.nil_append, String.Pos.Raw.extract.go₂, ite_eq_left hie]
  | cons y m ih =>
    intro i e he
    have hie : i ≠ e := by
      intro h
      rw [h, bl_cons] at he
      have := Char.utf8Size_pos y
      omega
    rw [List.cons_append, String.Pos.Raw.extract.go₂, ite_eq_right hie,
      ih (i + y) e (by rw [String.Pos.Raw.byteIdx_add_char, he, bl_cons]; omega)]

theorem go₁_append (p u : List Char) :
    ∀ (i b e : String.Pos.Raw), b.byteIdx = i.byteIdx + bl p →
      String.Pos.Raw.extract.go₁ (p ++ u) i b e = String.Pos.Raw.extract.go₂ u b e := by
  induction p with
  | nil =>
    intro i b e hb
    have hib : i = b := String.Pos.Raw.ext (by rw [bl_nil, Nat.add_zero] at hb; omega)
    cases u with
    | nil => rw [List.nil_append, String.Pos.Raw.extract.go₁, String.Pos.Raw.extract.go₂]
    | cons y u => rw [List.nil_append, String.Pos.Raw.extract.go₁, ite_eq_left hib, hib]
  | cons y p ih =>
    intro i b e hb
    have hib : i ≠ b := by
      intro h
      rw [h, bl_cons] at hb
      have := Char.utf8Size_pos y
      omega
    rw [List.cons_append, String.Pos.Raw.extract.go₁, ite_eq_right hib,
      ih (i + y) b e (by rw [String.Pos.Raw.byteIdx_add_char, hb, bl_cons]; omega)]

theorem extract_of_eq (s : String) (p m t : List Char) (hs : s.toList = p ++ m ++ t)
    (b e : String.Pos.Raw) (hb : b.byteIdx = bl p) (he : e.byteIdx = bl p + bl m) :
    String.Pos.Raw.extract s b e = String.ofList m := by
  show (if b.byteIdx ≥ e.byteIdx then "" else
    String.ofList (String.Pos.Raw.extract.go₁ s.toList 0 b e)) = String.ofList m
  by_cases hm : m = []
  · subst hm
    have hge : b.byteIdx ≥ e.byteIdx := by rw [hb, he, bl_nil]; omega
    rw [ite_eq_left hge, String.ofList_nil]
  · have hpos := bl_pos_of_ne_nil hm
    have hlt : ¬ (b.byteIdx ≥ e.byteIdx) := by rw [hb, he]; omega
    rw [ite_eq_right hlt, hs, List.append_assoc,
      go₁_append p (m ++ t) 0 b e (by rw [hb, String.Pos.Raw.byteIdx_zero, Nat.zero_add]),
      go₂_append m t b e (by rw [he, hb])]

theorem get_singleton_zero (c : Char) : String.Pos.Raw.get (String.singleton c) 0 = c :=
  get_of_eq _ [] c [] (by simp) 0 rfl

theorem next_singleton_zero (c : Char) :
    (String.Pos.Raw.next (String.singleton c) 0).byteIdx = c.utf8Size := by
  rw [next_of_eq _ [] c [] (by simp) 0 rfl, bl_nil, Nat.zero_add]

theorem atEnd_singleton_next (c : Char) :
    String.Pos.Raw.atEnd (String.singleton c) (String.Pos.Raw.next (String.singleton c) 0) = true :=
  (atEnd_of_eq _ [c] [] (by simp) _ (by rw [next_singleton_zero, bl_singleton])).2 rfl

theorem singleton_ne_empty (c : Char) : String.singleton c ≠ "" := by
  intro h
  have := congrArg String.toList h
  rw [String.toList_singleton, String.toList_empty] at this
  exact List.cons_ne_nil _ _ this

theorem splitOnAux_singleton (s : String) (c : Char) (t : List Char) :
    ∀ (p m : List Char) (b i : String.Pos.Raw) (r : List String),
      s.toList = p ++ m ++ t → c ∉ m → b.byteIdx = bl p → i.byteIdx = bl p + bl m →
      String.splitOnAux s (String.singleton c) b i 0 r =
        r.reverse ++ ((m ++ t).splitOn c).map String.ofList := by
  induction t with
  | nil =>
    intro p m b i r hs hc hb hi
    have hend : String.Pos.Raw.atEnd s i = true :=
      (atEnd_of_eq s (p ++ m) [] (by rw [hs, List.append_nil]) i (by rw [hi, bl_append])).2 rfl
    rw [String.splitOnAux, ite_eq_left hend]
    dsimp only
    rw [extract_of_eq s p m [] hs b i hb hi, List.append_nil, List.splitOn_eq_singleton hc]
    simp
  | cons x t ih =>
    intro p m b i r hs hc hb hi
    have hi' : i.byteIdx = bl (p ++ m) := by rw [hi, bl_append]
    have hnot : ¬ (String.Pos.Raw.atEnd s i = true) := by
      rw [atEnd_of_eq s (p ++ m) (x :: t) hs i hi']
      exact List.cons_ne_nil x t
    have hn := next_of_eq s (p ++ m) x t hs i hi'
    rw [String.splitOnAux, ite_eq_right hnot, get_of_eq s (p ++ m) x t hs i hi', get_singleton_zero]
    by_cases hxc : x = c
    · have hbeq : (x == c) = true := by simp [hxc]
      rw [ite_eq_left hbeq]
      dsimp only
      rw [ite_eq_left (atEnd_singleton_next c)]
      have he : ((String.Pos.Raw.next s i).unoffsetBy
          (String.Pos.Raw.next (String.singleton c) 0)).byteIdx = bl p + bl m := by
        rw [String.Pos.Raw.byteIdx_unoffsetBy, hn, next_singleton_zero, bl_append, hxc]
        omega
      rw [extract_of_eq s p m (x :: t) hs b _ hb he]
      have h1 : s.toList = (p ++ m ++ [x]) ++ [] ++ t := by rw [hs]; simp
      have h3 : (String.Pos.Raw.next s i).byteIdx = bl (p ++ m ++ [x]) := by
        simp only [hn, bl_append, bl_singleton] <;> omega
      have h4 : (String.Pos.Raw.next s i).byteIdx = bl (p ++ m ++ [x]) + bl [] := by
        rw [bl_nil, Nat.add_zero]; exact h3
      rw [ih (p ++ m ++ [x]) [] (String.Pos.Raw.next s i) (String.Pos.Raw.next s i)
        (String.ofList m :: r) h1 (by simp) h3 h4]
      rw [hxc, List.splitOn_append_cons_self_of_not_mem hc]
      simp
    · have hbeq : ¬ ((x == c) = true) := by simpa using hxc
      rw [ite_eq_right hbeq, String.Pos.Raw.unoffsetBy_zero]
      have h1 : s.toList = p ++ (m ++ [x]) ++ t := by rw [hs]; simp
      have h2 : c ∉ m ++ [x] := by
        intro h
        rw [List.mem_append, List.mem_singleton] at h
        rcases h with h | h
        · exact hc h
        · exact hxc h.symm
      have h4 : (String.Pos.Raw.next s i).byteIdx = bl p + bl (m ++ [x]) := by
        simp only [hn, bl_append, bl_singleton] <;> omega
      rw [ih p (m ++ [x]) b (String.Pos.Raw.next s i) r h1 h2 hb h4]
      simp

end SplitOnProof

open SplitOnProof in
theorem splitOn_singleton (s : String) (c : Char) :
    s.splitOn (String.singleton c) = (s.toList.splitOn c).map String.ofList := by
  have hne : ¬ ((String.singleton c == "") = true) := by
    rw [beq_iff_eq]; exact singleton_ne_empty c
  unfold String.splitOn
  rw [ite_eq_right hne]
  have := splitOnAux_singleton s c s.toList [] [] 0 0 [] (by simp) (by simp) rfl rfl
  rw [this]
  simp

theorem splitOn_space (s : String) :
    s.splitOn " " = (s.toList.splitOn ' ').map String.ofList := by
  rw [show (" " : String) = String.singleton ' ' by decide]
  exact splitOn_singleton s ' '

theorem splitOn_slash (s : String) :
    s.splitOn "/" = (s.toList.splitOn '/').map String.ofList := by
  rw [show ("/" : String) = String.singleton '/' by decide]
  exact splitOn_singleton s '/'

end NativeTrust.StrFast

#print axioms NativeTrust.StrFast.splitOn_space
#print axioms NativeTrust.StrFast.splitOn_slash
#print axioms NativeTrust.StrFast.splitOn_singleton

example (s : String) : s.splitOn " " = (s.toList.splitOn ' ').map String.ofList :=
  NativeTrust.StrFast.splitOn_space s
example (s : String) (c : Char) :
    s.splitOn (String.singleton c) = (s.toList.splitOn c).map String.ofList :=
  NativeTrust.StrFast.splitOn_singleton s c
