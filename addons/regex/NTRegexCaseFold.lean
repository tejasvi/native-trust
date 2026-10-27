import NativeTrust
import RegexCorrectness.Unicode.CaseFold.Data

/-!
# Kernel replacements for lean-regex's case-fold table checks (add-on, package-specific)

`checkAllPairs_isLtFirst_caseFoldRepresentatives` and `checkAllPairs_noChain_caseFoldRepresentatives`
decide `checkAllPairs (isLtFirst caseFoldRepresentatives.get)` and `checkAllPairs (noChain …)`: n² = 2.3M
pair checks over the 1,512-row table, each indexing an `Array` (linear in the kernel), after parsing the
table from a 15.7 KB string with the legacy byte-position `String.splitOn` (quadratic in the kernel).

* `String.splitOn` with a one-character separator is `List.splitOn` on the characters
  (`splitOn_singleton`, from the BerryEsseen add-on's `SplitOnSpace.lean`); `splitOnL` is that, and the
  legacy algorithm otherwise. Registered with `@[kernel_replace_retry]` (equation `splitOn_eq_splitOnL`).
* `checkAllPairs (isLtFirst arr)` holds iff the first components are strictly increasing, an O(n) check
  of adjacent pairs (`sortedFast`); `checkAllPairs (noChain arr)` iff no first component is a second
  component, an O(n) check against a bit set of the first components held in one natural number
  (`noChainFast`; `Nat.lor`/`Nat.shiftLeft`/`Nat.testBit` are GMP operations in the kernel). Both are
  proved for every array and registered as `@[kernel_fold]` patterns with `@[kernel_replace_retry]`
  equations. (Core's `List.mergeSort` would not do: it is well-founded recursion, which the replacement's
  evaluation does not get past.)

The package's definitions are private to its module (`module` system), so they are given public aliases
here (`capP`, `isLtFirstP`, `noChainP`: the same kernel constants), and the fold patterns are built from
the private constants themselves, as they occur in the decided terms.

Toolchain v4.34.0-rc1 (the package's pin; `splitOn_singleton` needs core ≥ 4.34). Compile to an olean in the
package's environment (`build_addon_v1.sh`) and pass `--extra-path <dir> --extra-import NTRegexCaseFold` to the
driver. With it both facts convert (28.9 GB and 215 s each; the parse is most of it).
-/

namespace NTRegex

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

/-! ## `String.splitOn` through `List.splitOn` -/

/-- `String.splitOn` (legacy): on a one-character separator, `List.splitOn` on the characters (linear in
the kernel), otherwise core's byte-position algorithm. -/
def splitOnL (s sep : String) : List String :=
  match NativeTrust.toListFast sep with
  | [c] => ((NativeTrust.toListFast s).splitOn c).map NativeTrust.ofListFast
  | _ => if sep == "" then [s] else String.splitOnAux s sep 0 0 0 []

@[kernel_replace_retry] theorem splitOn_eq_splitOnL : @String.splitOn = @splitOnL := by
  funext s sep
  unfold splitOnL
  split
  · next c h =>
    rw [NativeTrust.toListFast_eq] at h
    have hsep : sep = String.singleton c :=
      String.toList_injective (by rw [h, String.toList_singleton])
    subst hsep
    rw [splitOn_singleton, NativeTrust.toListFast_eq, NativeTrust.ofList_eq_ofListFast']
  · rfl

/-! ## Public aliases of the package's private definitions -/

open Lean Meta in
run_meta do
  let priv (n : Name) : Name := (Name.mkNum (`_private ++ `RegexCorrectness.Unicode.CaseFold.Data) 0) ++ n
  for (a, n) in [(`NTRegex.capP, `Regex.Unicode.checkAllPairs), (`NTRegex.isLtFirstP, `Regex.Unicode.isLtFirst),
      (`NTRegex.noChainP, `Regex.Unicode.noChain)] do
    let p := priv n
    let some ci := (← getEnv).find? p | throwError "NTRegex: no constant {p}"
    let decl := Declaration.defnDecl { name := a, levelParams := ci.levelParams, type := ci.type, value := mkConst p (ci.levelParams.map mkLevelParam), hints := .abbrev, safety := .safe }
    addDecl decl

/-! ## `checkAllPairs` -/

/-- The package's `checkAllPairs`, verbatim (so that the kernel sees it equal to the original). -/
def cap {n : Nat} (f : Fin n → Fin n → Bool) : Bool :=
  let rec go₂ (i : Nat) (hi : i ≤ n) (j : Fin n) : Bool :=
    if _ : i ≥ n then true else
    f ⟨i, by grind⟩ j && go₂ (i + 1) (by grind) j
  let rec go₁ (j : Nat) (hj : j ≤ n) : Bool :=
    if _ : j ≥ n then true else
    go₂ 0 (by grind) ⟨j, by grind⟩ && go₁ (j + 1) (by grind)
  go₁ 0 (by grind)

def isLtFirstC (arr : Array (Char × Char)) (i j : Fin arr.size) : Bool :=
  decide (i < j → arr[i].1 < arr[j].1)

def noChainC (arr : Array (Char × Char)) (i j : Fin arr.size) : Bool :=
  decide (arr[i].1 ≠ arr[j].2)

-- checked by the kernel only (by unfolding both sides)
open Lean Meta in
run_meta do
  for (a, b, t) in [(`NTRegex.capP, `NTRegex.cap, `NTRegex.capP_eq), (`NTRegex.isLtFirstP, `NTRegex.isLtFirstC, `NTRegex.isLtFirstP_eq),
      (`NTRegex.noChainP, `NTRegex.noChainC, `NTRegex.noChainP_eq)] do
    let ty ← mkEq (mkConst a) (mkConst b)
    let decl := Declaration.thmDecl { name := t, levelParams := [], type := ty, value := ← mkEqRefl (mkConst a) }
    addDecl decl

theorem cap_go₂ {n : Nat} {f : Fin n → Fin n → Bool} (i : Nat) (hi : i ≤ n) (j : Fin n) :
    cap.go₂ f i hi j = true ↔ ∀ k : Fin n, i ≤ k.val → f k j = true := by
  fun_induction cap.go₂ f i hi j <;> grind

theorem cap_go₁ {n : Nat} {f : Fin n → Fin n → Bool} (j : Nat) (hj : j ≤ n) :
    cap.go₁ f j hj = true ↔ ∀ i k : Fin n, j ≤ k.val → f i k = true := by
  fun_induction cap.go₁ f j hj
  next j hj h =>
    simp only [true_iff]
    intro i k hk
    have := k.isLt
    omega
  next j hj h ih =>
    rw [Bool.and_eq_true, cap_go₂, ih]
    constructor
    · rintro ⟨h1, h2⟩ i k hk
      by_cases hkj : k.val = j
      · have hk' : k = ⟨j, by omega⟩ := Fin.ext hkj
        rw [hk']
        exact h1 i (Nat.zero_le _)
      · exact h2 i k (by omega)
    · intro h'
      exact ⟨fun k _ => h' k _ (Nat.le_refl _), fun i k hk => h' i k (by omega)⟩

theorem cap_iff {n : Nat} {f : Fin n → Fin n → Bool} : cap f = true ↔ ∀ i j, f i j = true := by
  unfold cap
  rw [cap_go₁]
  grind

/-! ## Sorted first components: adjacent pairs -/

def sortedL : List (Char × Char) → Bool
  | a :: b :: rest => decide (a.1 < b.1) && sortedL (b :: rest)
  | _ => true

theorem sortedL_iff : ∀ l : List (Char × Char), sortedL l = true ↔ l.Pairwise (fun a b => a.1 < b.1)
  | [] => by simp [sortedL]
  | [a] => by simp [sortedL]
  | a :: b :: rest => by
    rw [sortedL, Bool.and_eq_true, decide_eq_true_eq, sortedL_iff (b :: rest)]
    constructor
    · rintro ⟨hab, hp⟩
      refine List.Pairwise.cons ?_ hp
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact Char.lt_trans hab ((List.pairwise_cons.1 hp).1 x hx)
    · intro h
      exact ⟨(List.pairwise_cons.1 h).1 b (List.mem_cons_self ..), (List.pairwise_cons.1 h).2⟩

def sortedFast (arr : Array (Char × Char)) : Bool := sortedL arr.toList

theorem cap_isLtFirst (arr : Array (Char × Char)) : cap (isLtFirstC arr) = sortedFast arr := by
  apply Bool.eq_iff_iff.2
  rw [cap_iff, sortedFast, sortedL_iff, List.pairwise_iff_getElem]
  constructor
  · intro h i j hi hj hij
    have hi' : i < arr.size := by simpa using hi
    have hj' : j < arr.size := by simpa using hj
    have := h ⟨i, hi'⟩ ⟨j, hj'⟩
    simp only [isLtFirstC, decide_eq_true_eq, Fin.mk_lt_mk, Fin.getElem_fin] at this
    rw [Array.getElem_toList, Array.getElem_toList]
    exact this hij
  · intro h i j
    simp only [isLtFirstC, decide_eq_true_eq, Fin.getElem_fin, Fin.lt_def]
    intro hij
    have := h i.val j.val (by simp) (by simp) hij
    rw [Array.getElem_toList, Array.getElem_toList] at this
    exact this

/-! ## No first component is a second component: a bit set of the first components -/

/-- The bits `c.toNat` of the characters of `l`, set in `m` (`Nat.lor`, `Nat.shiftLeft`: GMP operations in the
kernel). -/
def charMask (l : List Char) (m : Nat) : Nat := l.foldl (fun m c => m ||| (1 <<< c.toNat)) m

theorem testBit_charMask : ∀ (l : List Char) (m k : Nat),
    (charMask l m).testBit k = (m.testBit k || l.any (fun c => c.toNat == k))
  | [], m, k => by simp [charMask]
  | c :: l, m, k => by
    have ih := testBit_charMask l (m ||| (1 <<< c.toNat)) k
    unfold charMask at ih ⊢
    rw [List.foldl_cons, ih, Nat.testBit_or, Nat.one_shiftLeft, Nat.testBit_two_pow, List.any_cons]
    cases m.testBit k <;> cases h : (c.toNat == k) <;> simp_all

/-- Is no first component a second component? One bit set, then one test per second component. -/
def noChainFast (arr : Array (Char × Char)) : Bool :=
  let m := charMask (arr.toList.map (·.1)) 0
  (arr.toList.map (·.2)).all fun c => !(m.testBit c.toNat)

theorem noChainFast_iff (arr : Array (Char × Char)) :
    noChainFast arr = true ↔ ∀ p ∈ arr.toList, ∀ q ∈ arr.toList, p.1 ≠ q.2 := by
  unfold noChainFast
  rw [List.all_eq_true]
  constructor
  · intro h p hp q hq hpq
    have := h q.2 (List.mem_map_of_mem hq)
    rw [testBit_charMask, Nat.zero_testBit, Bool.false_or, Bool.not_eq_true', List.any_eq_false] at this
    exact this p.1 (List.mem_map_of_mem hp) (by rw [hpq]; exact beq_self_eq_true _)
  · intro h c hc
    rw [testBit_charMask, Nat.zero_testBit, Bool.false_or, Bool.not_eq_true', List.any_eq_false]
    intro x hx hxc
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hc
    obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hx
    exact h p hp q hq (Char.toNat_inj.1 (beq_iff_eq.1 hxc))

theorem cap_noChain (arr : Array (Char × Char)) : cap (noChainC arr) = noChainFast arr := by
  apply Bool.eq_iff_iff.2
  rw [cap_iff, noChainFast_iff]
  simp only [noChainC, decide_eq_true_eq]
  constructor
  · intro h p hp q hq
    obtain ⟨i, hi, rfl⟩ := List.mem_iff_getElem.1 hp
    obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.1 hq
    simpa using h ⟨i, by simpa using hi⟩ ⟨j, by simpa using hj⟩
  · intro h i j
    exact h arr[i] (by simp) arr[j] (by simp)

/-! ## Fold patterns and replacements -/

noncomputable def sortedPatA (arr : Array (Char × Char)) : Bool := capP (isLtFirstP arr)
noncomputable def noChainPatA (arr : Array (Char × Char)) : Bool := capP (noChainP arr)

-- the patterns over the private constants themselves, as they occur in the decided terms
open Lean Meta in
run_meta do
  let priv (n : Name) : Name := (Name.mkNum (`_private ++ `RegexCorrectness.Unicode.CaseFold.Data) 0) ++ n
  let subst : NameMap Name := ({} : NameMap Name) |>.insert `NTRegex.capP (priv `Regex.Unicode.checkAllPairs)
    |>.insert `NTRegex.isLtFirstP (priv `Regex.Unicode.isLtFirst) |>.insert `NTRegex.noChainP (priv `Regex.Unicode.noChain)
  for (a, p) in [(`NTRegex.sortedPatA, `NTRegex.sortedPat), (`NTRegex.noChainPatA, `NTRegex.noChainPat)] do
    let some (.defnInfo d) := (← getEnv).find? a | throwError "NTRegex: no {a}"
    let value := d.value.replace fun | .const n us => (subst.find? n).map (mkConst · us) | _ => none
    let decl := Declaration.defnDecl { name := p, levelParams := [], type := d.type, value, hints := d.hints, safety := .safe }
    addDecl decl

attribute [kernel_fold] sortedPat noChainPat

@[kernel_replace_retry] theorem sortedPat_eq : @sortedPat = @sortedFast := by
  funext arr
  show capP (isLtFirstP arr) = sortedFast arr
  rw [capP_eq, isLtFirstP_eq]
  exact cap_isLtFirst arr

@[kernel_replace_retry] theorem noChainPat_eq : @noChainPat = @noChainFast := by
  funext arr
  show capP (noChainP arr) = noChainFast arr
  rw [capP_eq, noChainP_eq]
  exact cap_noChain arr

end NTRegex

#print axioms NTRegex.splitOn_eq_splitOnL
#print axioms NTRegex.sortedPat_eq
#print axioms NTRegex.noChainPat_eq
