import NativeTrust
import Compiler.ObjectiveBendC4Vectors

/-!
# Kernel replacement for minidregg's C4 linearization (add-on, package-specific)

`Minidregg.Compiler.ObjectiveBendC4.linearize` counts the members of precedence lists in a
`Std.HashMap String Int` and indexes the suffix tail in a `Std.HashMap String Nat`. `String.hash` has no
kernel definition, so the kernel cannot evaluate it (`Compiler.ObjectiveBendC4Vectors`: 5 facts).

The function reads its maps only through `getD`, `get?` and `contains` and writes them only with `insert`,
so its result does not depend on the hash function. `linearizeL` is the same code over association lists
(`lookup`; `insert` is `cons`). `linearize_eq : linearize = linearizeL`, registered with
`@[kernel_replace_retry]`, lets the retry evaluate it instead.

The proof is a simulation. Every hash map the original builds is `toHM l` for the list `l` the copy builds
(`toHM` inserts a list's entries into `∅`, so `toHM (linsert l k v) = (toHM l).insert k v` by `rfl`).
`getD`, `get?` and `contains` of `toHM l` are the list lookups (core's `getElem?_insert`), and each `for`
loop of the original is the copy's loop with the state mapped (`forIn_sim`).

`table_eq` and `expected_eq` (also `@[kernel_replace_retry]`) give the vector file's two string tables as
parsed lists, so that the facts do not parse them with `String.splitOn` in every kernel check.
-/

namespace NTMinidregg
open Minidregg.Compiler.ObjectiveBendC4

def lgetD {V : Type} (m : List (String × V)) (k : String) (d : V) : V := (m.lookup k).getD d
def linsert {V : Type} (m : List (String × V)) (k : String) (v : V) : List (String × V) := (k, v) :: m
def lcontains {V : Type} (m : List (String × V)) (k : String) : Bool := (m.lookup k).isSome

/-- The hash map with the entries of an association list (later entries shadowed by earlier ones). -/
def toHM {V : Type} (l : List (String × V)) : Std.HashMap String V := l.foldr (fun p m => m.insert p.1 p.2) ∅

theorem getElem?_toHM {V : Type} (l : List (String × V)) (a : String) : (toHM l)[a]? = l.lookup a := by
  induction l with
  | nil => simp [toHM]
  | cons p l ih =>
    obtain ⟨k, v⟩ := p
    show ((toHM l).insert k v)[a]? = List.lookup a ((k, v) :: l)
    rw [Std.HashMap.getElem?_insert, ih, List.lookup_cons]
    by_cases h : k = a
    · subst h; simp
    · rw [beq_false_of_ne h, beq_false_of_ne (Ne.symm h)]; rfl

theorem getD_toHM {V : Type} (l : List (String × V)) (k : String) (d : V) : (toHM l).getD k d = lgetD l k d := by
  rw [Std.HashMap.getD_eq_getD_getElem?, getElem?_toHM, lgetD]

theorem get?_toHM {V : Type} (l : List (String × V)) (k : String) : (toHM l).get? k = l.lookup k := by
  rw [Std.HashMap.get?_eq_getElem?, getElem?_toHM]

theorem contains_toHM {V : Type} (l : List (String × V)) (k : String) : (toHM l).contains k = lcontains l k := by
  rw [Std.HashMap.contains_eq_isSome_getElem?, getElem?_toHM, lcontains]

theorem insert_toHM {V : Type} (l : List (String × V)) (k : String) (v : V) :
    (toHM l).insert k v = toHM (linsert l k v) := rfl

theorem empty_toHM {V : Type} : (∅ : Std.HashMap String V) = toHM [] := rfl

def removeSuffixTailAndReverseL (tailIndex : List (String × Nat)) : List String → Int → Except String (List String)
  | [], _ => .ok []
  | c :: rest, suffixPos =>
    match tailIndex.lookup c with
    | none =>
      let taken := rest.takeWhile (fun x => !lcontains tailIndex x)
      let remaining := rest.drop taken.length
      match remaining with
      | [] => .ok (taken.reverse ++ [c])
      | x :: _ => .error ("ancestor out of order versus suffix tail " ++ x)
    | some p =>
      if (p : Int) > suffixPos then removeSuffixTailAndReverseL tailIndex rest p
      else .error ("ancestor out of order versus suffix tail " ++ c)

theorem removeSuffix_toHM (l : List (String × Nat)) :
    ∀ xs p, removeSuffixTailAndReverse (toHM l) xs p = removeSuffixTailAndReverseL l xs p
  | [], _ => by simp [removeSuffixTailAndReverse, removeSuffixTailAndReverseL]
  | c :: rest, p => by
    simp only [removeSuffixTailAndReverse, removeSuffixTailAndReverseL, get?_toHM, contains_toHM]
    cases List.lookup c l with
    | none => rfl
    | some q => simp only [removeSuffix_toHM l rest]

def linearizeL (g : Graph) (head : List String) (parentsIn : List (List String)) :
    Except Refusal (List String × Option String) := do
  let parents := parentsIn.filter (fun chain => !chain.isEmpty)
  match parents with
  | [] => return (head, none)
  | [[parent]] => return (head ++ g.precedence parent,
      if g.isSuffix parent then some parent else superSuffix g parent)
  | _ =>
  let fuel := suffixFuel g parents
  let mut rcandidates : List (List String) := []
  let mut ss : Option String := none
  let mut ssTail : List String := []
  let mut counts : List (String × Int) := []
  for chain in parents do
    for parent in chain do
      if lgetD counts parent 0 != 0 then continue
      let al := g.precedence parent
      let pre := al.takeWhile (fun x => !g.isSuffix x)
      let rest := al.drop pre.length
      for x in pre do counts := linsert counts x (lgetD counts x 0 + 1)
      match rest with
      | [] => pure ()
      | s :: _ =>
        let merged ← match mergeSuffix g fuel (some s) ss with
          | .ok v => pure v
          | .error e => suffixRefusal head e
        if merged != ss then
          for t in (rest.takeWhile (fun t => some t != ss)) do
            counts := linsert counts t (lgetD counts t 0 + 1)
          ss := merged
          ssTail := rest
      if !pre.isEmpty then rcandidates := pre.reverse :: rcandidates
  let mut tailIndex : List (String × Nat) := []
  let mut position := ssTail.length
  for t in ssTail do
    tailIndex := linsert tailIndex t position
    position := position - 1
  let rLocalOrder := (parents.filter (fun chain => chain.length > 1)).map List.reverse
  for chain in rLocalOrder do
    for c in chain do counts := linsert counts c (lgetD counts c 0 + 1)
  rcandidates := rLocalOrder ++ rcandidates
  let mut cleaned : List (List String) := []
  for rcl in rcandidates do
    match removeSuffixTailAndReverseL tailIndex rcl (-1) with
    | .ok l => if !l.isEmpty then cleaned := cleaned ++ [l]
    | .error e => inconsistent head e
  let candidates := cleaned.reverse
  for cl in candidates do
    match cl with
    | c :: _ => counts := linsert counts c (lgetD counts c 0 - 1)
    | [] => pure ()
  let mut out := head
  let mut tails := candidates
  for _ in List.range (mergeFuel candidates) do
    match tails with
    | [] => return (out ++ ssTail, ss)
    | [only] => return (out ++ only ++ ssTail, ss)
    | _ =>
      let some winner := tails.find? (fun t => match t with | c :: _ => lgetD counts c 0 == 0 | [] => false)
        | inconsistent head "no C3 candidate"
      let next := winner.head!
      out := out ++ [next]
      let mut updated : List (List String) := []
      for t in tails do
        match t with
        | c :: rest' =>
          if c == next then
            match rest' with
            | d :: _ => counts := linsert counts d (lgetD counts d 0 - 1)
            | [] => pure ()
            if !rest'.isEmpty then updated := updated ++ [rest']
          else updated := updated ++ [t]
        | [] => pure ()
      tails := updated
  .error (.fuelExhausted "merge loop" head)


/-! ## Simulation of the loops -/

/-- `ForInStep` with the state mapped. -/
def stepMap {σ₁ σ₂ : Type} (φ : σ₂ → σ₁) : ForInStep σ₂ → ForInStep σ₁
  | .done s => .done (φ s)
  | .yield s => .yield (φ s)

theorem forIn_sim {ε γ σ₁ σ₂ : Type} (φ : σ₂ → σ₁) (xs : List γ)
    (f₁ : γ → σ₁ → Except ε (ForInStep σ₁)) (f₂ : γ → σ₂ → Except ε (ForInStep σ₂))
    (hf : ∀ x s, f₁ x (φ s) = stepMap φ <$> f₂ x s) (s : σ₂) :
    forIn xs (φ s) f₁ = φ <$> forIn xs s f₂ := by
  induction xs generalizing s with
  | nil => simp
  | cons x xs ih =>
    rw [List.forIn_cons, List.forIn_cons, hf]
    cases f₂ x s with
    | error e => rfl
    | ok st =>
      cases st with
      | done b => rfl
      | yield b => exact ih b

theorem bind_sim {ε α₁ α₂ β₁ β₂ : Type} (φ : α₂ → α₁) {F : β₂ → β₁} {x₁ : Except ε α₁} {x₂ : Except ε α₂}
    {k₁ : α₁ → Except ε β₁} {k₂ : α₂ → Except ε β₂} (hx : x₁ = φ <$> x₂) (hk : ∀ a, k₁ (φ a) = F <$> k₂ a) :
    x₁ >>= k₁ = F <$> (x₂ >>= k₂) := by
  subst hx
  cases x₂ with
  | error e => rfl
  | ok a => exact hk a

theorem bind_sim_eq {ε α₁ α₂ β : Type} (φ : α₂ → α₁) {x₁ : Except ε α₁} {x₂ : Except ε α₂}
    {k₁ : α₁ → Except ε β} {k₂ : α₂ → Except ε β} (hx : x₁ = φ <$> x₂) (hk : ∀ a, k₁ (φ a) = k₂ a) :
    x₁ >>= k₁ = x₂ >>= k₂ := by
  subst hx
  cases x₂ with
  | error e => rfl
  | ok a => exact hk a

/-! The matchers of `linearizeL` on map-free types are those of `linearize`. -/
theorem m1 : @linearizeL.match_1 = @linearize.match_1 := rfl
theorem m5 : @linearizeL.match_5 = @linearize.match_5 := rfl
theorem m7 : @linearizeL.match_7 = @linearize.match_7 := rfl
theorem m11 : @linearizeL.match_11 = @linearize.match_11 := rfl
theorem m14 : @linearizeL.match_14 = @linearize.match_14 := rfl
theorem m17 : @linearizeL.match_17 = @linearize.match_17 := rfl
theorem m23 : @linearizeL.match_23 = @linearize.match_23 := rfl

abbrev Map1 := MProd (Std.HashMap String Int) (MProd (List (List String)) (MProd (Option String) (List String)))
abbrev Lst1 := MProd (List (String × Int)) (MProd (List (List String)) (MProd (Option String) (List String)))
def Φ1 (s : Lst1) : Map1 := ⟨toHM s.1, s.2⟩
def Φ5 (s : MProd Nat (List (String × Nat))) : MProd Nat (Std.HashMap String Nat) := ⟨s.1, toHM s.2⟩
def Φ10 (s : MProd (Option (List String × Option String)) (MProd (List (String × Int)) (MProd (List String) (List (List String))))) :
    MProd (Option (List String × Option String)) (MProd (Std.HashMap String Int) (MProd (List String) (List (List String)))) :=
  ⟨s.1, toHM s.2.1, s.2.2⟩
def Φ11 (s : MProd (List (String × Int)) (List (List String))) : MProd (Std.HashMap String Int) (List (List String)) :=
  ⟨toHM s.1, s.2⟩

@[kernel_replace_retry] theorem linearize_eq : @linearize = @linearizeL := by
  funext g head parentsIn
  simp only [linearize, linearizeL]
  rw [m23, m1, m5, m7, m11, m14, m17]
  congr 1
  funext x
  refine bind_sim_eq Φ1 (forIn_sim Φ1 _ _ _ ?_ ⟨[], [], none, []⟩) ?_
  · -- the loop over the parent chains
    intro chain ⟨l, rc, ss, st⟩
    simp only [Φ1]
    refine bind_sim Φ1 (forIn_sim Φ1 _ _ _ ?_ ⟨l, rc, ss, st⟩) ?_
    · -- the loop over one chain
      intro parent ⟨l, rc, ss, st⟩
      simp only [Φ1, getD_toHM]
      split
      · rfl
      · simp only [pure_bind]
        refine bind_sim toHM (forIn_sim toHM _ _ _ ?_ l) ?_
        · intro x l'; simp only [getD_toHM, insert_toHM]; rfl
        · intro l'
          split
          next heq =>
            simp only [heq]
            split <;> rfl
          next s tail heq =>
            simp only [heq]
            split
            next v heq2 =>
              try simp only [heq2]
              split
              · refine bind_sim toHM (forIn_sim toHM _ _ _ ?_ l') ?_
                · intro t l''; simp only [getD_toHM, insert_toHM]; rfl
                · intro l''; split <;> rfl
              · split <;> rfl
            next e heq2 =>
              try simp only [heq2]
              refine bind_sim id (id_map _).symm ?_
              intro v
              simp only [id]
              split
              · refine bind_sim toHM (forIn_sim toHM _ _ _ ?_ l') ?_
                · intro t l''; simp only [getD_toHM, insert_toHM]; rfl
                · intro l''; split <;> rfl
              · split <;> rfl
    · intro ⟨l, rc, ss, st⟩; rfl
  · intro ⟨l, rc, ss, st⟩
    simp only [Φ1]
    -- the suffix-tail index
    refine bind_sim_eq Φ5 (forIn_sim Φ5 _ _ _ ?_ ⟨st.length, []⟩) ?_
    · intro t ⟨p, ti⟩; simp only [Φ5, pure_bind, insert_toHM]; rfl
    · intro ⟨p, ti⟩
      simp only [Φ5]
      -- the local orders
      refine bind_sim_eq toHM (forIn_sim toHM _ _ _ ?_ l) ?_
      · intro chain l'
        refine bind_sim toHM (forIn_sim toHM _ _ _ ?_ l') ?_
        · intro c l''; simp only [pure_bind, getD_toHM, insert_toHM]; rfl
        · intro l''; rfl
      · intro l'
        simp only [removeSuffix_toHM]
        -- the cleaned candidates (no map in the state)
        refine bind_sim_eq id (id_map _).symm ?_
        intro cleaned
        simp only [id]
        -- the candidates' heads
        refine bind_sim_eq toHM (forIn_sim toHM _ _ _ ?_ l') ?_
        · intro cl l''
          rcases cl with _ | ⟨c, tl⟩
          · rfl
          · simp only [pure_bind, getD_toHM, insert_toHM]; rfl
        · intro l''
          -- the merge loop
          refine bind_sim_eq Φ10 (forIn_sim Φ10 _ _ _ ?_ ⟨none, l'', head, cleaned.reverse⟩) ?_
          · intro n ⟨o, lc, out, tails⟩
            rcases tails with _ | ⟨t1, _ | ⟨t2, tr⟩⟩
            · rfl
            · rfl
            · simp only [Φ10, getD_toHM]
              split
              next winner heq =>
                try simp only [heq]
                refine bind_sim Φ11 (forIn_sim Φ11 _ _ _ ?_ ⟨lc, []⟩) ?_
                · intro t ⟨lc', upd⟩
                  rcases t with _ | ⟨c, _ | ⟨d, tl⟩⟩
                  · rfl
                  · simp only [Φ11]; split <;> (try simp only [pure_bind]) <;> (try split) <;> rfl
                  · simp only [Φ11, getD_toHM, insert_toHM]; split <;> (try simp only [pure_bind]) <;> (try split) <;> rfl
                · intro ⟨lc', upd⟩; rfl
              next =>
                refine bind_sim id (id_map _).symm ?_
                intro u; rfl
          · intro ⟨o, lc, out, tails⟩
            cases o <;> rfl

/-! ## The vector tables as literals

`ObjectiveBendC4Vectors.table` and `.expected` are parsed from string literals with `String.splitOn`. The
kernel evaluates that slowly (minutes for `expected`), and again in every piece of a structured check. The
equations below, proved with `kdecide` once when this file is compiled, let the retry use the parsed lists. -/

/-- `Minidregg.Compiler.ObjectiveBendC4Vectors.table`, parsed. -/
def tableL : List (String × List String) :=
  [("O", []), ("A", ["O"]), ("B", ["O"]), ("C", ["O"]), ("D", ["O"]), ("E", ["O"]), ("K1", ["A", "B", "C"]),
   ("K2", ["D", "B", "E"]), ("K3", ["D", "A"]), ("Z", ["K1", "K2", "K3"]), ("J1", ["C", "A", "B"]),
   ("J2", ["B", "D", "E"]), ("J3", ["A", "D"]), ("Y", ["J1", "J3", "J2"]), ("DB", ["B"]), ("WB", ["B"]),
   ("EL", ["DB"]), ("SM", ["DB"]), ("PWB", ["EL", "WB"]), ("SC", ["SM"]), ("P", ["PWB", "SC"]), ("GL", ["O"]),
   ("HG", ["GL"]), ("VG", ["GL"]), ("HVG", ["HG", "VG"]), ("VHG", ["VG", "HG"]), ("HH", []), ("GG", ["HH"]),
   ("II", ["GG"]), ("FF", ["HH"]), ("EE", ["HH"]), ("DD", ["FF"]), ("CC", ["EE", "FF", "GG"]), ("BB", []),
   ("AA", ["BB", "CC", "DD"]), ("o", ["O"]), ("a", ["o"]), ("b", ["a"]), ("c", ["b", "o"]), ("d", ["D", "c"]),
   ("M", ["A", "B", "b", "a"]), ("N", ["C", "c"]), ("L", ["M", "N"]), ("k", ["D", "L"]), ("j", ["E", "k", "A"]),
   ("I", ["N", "M"]), ("x1", []), ("x2", ["x1"]), ("x3", ["x2"]), ("x4", ["x3"]), ("x5", ["x4", "x1"]),
   ("SBA", []), ("SBB", []), ("SBS", ["SBA"]), ("sBs", ["SBA"]), ("SBC", ["SBS", "SBB"])]

/-- `Minidregg.Compiler.ObjectiveBendC4Vectors.expected`, parsed. -/
def expectedL : List String :=
  ["O", "A O", "B O", "C O", "D O", "E O", "K1 A B C O", "K2 D B E O", "K3 D A O", "Z K1 K2 K3 D A B C E O",
   "J1 C A B O", "J2 B D E O", "J3 A D O", "Y J1 C J3 A J2 B D E O", "DB B O", "WB B O", "EL DB B O", "SM DB B O",
   "PWB EL DB WB B O", "SC SM DB B O", "P PWB EL SC SM DB WB B O", "GL O", "HG GL O", "VG GL O", "HVG HG VG GL O",
   "VHG VG HG GL O", "HH", "GG HH", "II GG HH", "FF HH", "EE HH", "DD FF HH", "CC EE FF GG HH", "BB",
   "AA BB CC EE DD FF GG HH", "o O", "a o O", "b a o O", "c b a o O", "d D c b a o O", "M A B b a o O",
   "N C c b a o O", "L M A B N C c b a o O", "k D L M A B N C c b a o O", "j E k D L M A B N C c b a o O",
   "I N C M A B c b a o O", "x1", "x2 x1", "x3 x2 x1", "x4 x3 x2 x1", "x5 x4 x3 x2 x1", "SBA", "SBB", "SBS SBA",
   "sBs SBA", "SBC SBS SBA SBB"]

set_option maxHeartbeats 0 in
theorem table_dec : decide (Minidregg.Compiler.ObjectiveBendC4Vectors.table = tableL) = true := by kdecide

@[kernel_replace_retry] theorem table_eq : @Minidregg.Compiler.ObjectiveBendC4Vectors.table = @tableL :=
  of_decide_eq_true table_dec

set_option maxHeartbeats 0 in
theorem expected_dec : decide (Minidregg.Compiler.ObjectiveBendC4Vectors.expected = expectedL) = true := by kdecide

@[kernel_replace_retry] theorem expected_eq : @Minidregg.Compiler.ObjectiveBendC4Vectors.expected = @expectedL :=
  of_decide_eq_true expected_dec

end NTMinidregg

#print axioms NTMinidregg.linearize_eq
#print axioms NTMinidregg.table_eq
#print axioms NTMinidregg.expected_eq
