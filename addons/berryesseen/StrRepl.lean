import NativeTrust

/-!
# StrRepl: list-based replacements for iterator-based `String` functions

Add-on to NativeTrust (toolchain `v4.34.0-rc2`). In this toolchain `String.toNat?`,
`String.toInt?`, `String.isNat`, `String.isInt`, `String.foldl`, ... are implemented on
`String.Slice`, whose loops run on `Std.Iter` (`WellFounded.extrinsicFix₃`, state types through
`Std.Shrink`), so the kernel cannot evaluate them.

The constants replaced here have types without `Std.Shrink` and without type-class arguments,
so `@[kernel_replace]` (constant ↦ constant, equation `@f = @g`) applies: each replacement runs
over `s.copy.toList`, and each equation is proved from core's
`String.Slice.foldl_eq_foldl_toList`, `String.Slice.foldr_eq_foldr_toList` and
`String.Slice.forIn_eq_forIn_toList`. Callers (`String.Slice.toNat?`, `String.toNat?`,
`String.Slice.toInt?`, `String.toInt?`, user parsers, ...) are then copied by NativeTrust with
the replacements substituted and bridged back by congruence.

Not covered (see `NOTES` in the report): the pattern-generic functions `String.replace`,
`String.contains`, `String.splitToList`, ... take the searcher (`ρ`, `σ`, `Std.Iterator`,
`Std.IteratorLoop`, `ToForwardSearcher` instances) as arguments, so no constant-level
replacement can specialise them.
-/

namespace NativeTrust.StrRepl

universe u

/-- `String.Slice.foldl` over the slice's character list. -/
def sliceFoldl {α : Type u} (f : α → Char → α) (init : α) (s : String.Slice) : α :=
  s.copy.toList.foldl f init

@[kernel_replace] theorem sliceFoldl_eq : @String.Slice.foldl.{u} = @sliceFoldl.{u} := by
  funext α f init s
  exact String.Slice.foldl_eq_foldl_toList

/-- `String.Slice.foldr` over the slice's character list. -/
def sliceFoldr {α : Type u} (f : Char → α → α) (init : α) (s : String.Slice) : α :=
  s.copy.toList.foldr f init

@[kernel_replace] theorem sliceFoldr_eq : @String.Slice.foldr.{u} = @sliceFoldr.{u} := by
  funext α f init s
  exact String.Slice.foldr_eq_foldr_toList

/-- The loop of `String.Slice.isNat`, verbatim, over a character list. -/
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

/-- `String.Slice.isNat` over the slice's character list. -/
def sliceIsNat (s : String.Slice) : Bool :=
  isNatList s.copy.toList

@[kernel_replace] theorem sliceIsNat_eq : @String.Slice.isNat = @sliceIsNat := by
  funext s
  simp only [String.Slice.isNat, sliceIsNat, isNatList, String.Slice.forIn_eq_forIn_toList]

/-- `List.toByteArray` without its `push` loop. The kernel turns a string literal into
`String.ofList l`, whose bytes are `(l.flatMap String.utf8EncodeChar).toByteArray`; with the core
definition (`loop` with `ByteArray.push`, each push a `List.concat`) that costs time and memory
quadratic in the length of the literal. -/
def toByteArrayFast (l : List UInt8) : ByteArray := ⟨l.toArray⟩

@[kernel_replace] theorem toByteArray_eq : @List.toByteArray = @toByteArrayFast := by
  funext l
  exact ByteArray.ext List.data_toByteArray

/-! Monomorphic list-based forms of `String.toNat?` / `String.toInt?`, with bodies that mention
no replaced constant. NativeTrust uses a replacement's body as it is (it does not copy it), so a
caller-level replacement (e.g. of a package's own parser) must call these, not `String.toNat?`. -/

def toNatOfList? (l : List Char) : Option Nat :=
  if isNatList l then
    some (l.foldl (fun n c => if c = '_' then n else n * 10 + (c.toNat - '0'.toNat)) 0)
  else
    none

theorem sliceToNat?_eq_list (s : String.Slice) : s.toNat? = toNatOfList? s.copy.toList := by
  have h : s.isNat = isNatList s.copy.toList := congrFun sliceIsNat_eq s
  simp only [String.Slice.toNat?, toNatOfList?, String.Slice.foldl_eq_foldl_toList, h]

theorem toNat?_eq_list (s : String) : s.toNat? = toNatOfList? s.toList := by
  rw [String.toNat?, sliceToNat?_eq_list, String.copy_toSlice]

def toIntOfSlice? (s : String.Slice) : Option Int :=
  match s.dropPrefix? '-' with
  | some rest => (toNatOfList? rest.copy.toList).map Int.negOfNat
  | none => (toNatOfList? s.copy.toList).map Int.ofNat

theorem sliceToInt?_eq (s : String.Slice) : s.toInt? = toIntOfSlice? s := by
  unfold String.Slice.toInt? toIntOfSlice?
  cases s.dropPrefix? '-' <;> simp only [sliceToNat?_eq_list]

theorem toInt?_eq (s : String) : s.toInt? = toIntOfSlice? s.toSlice := by
  rw [String.toInt?, sliceToInt?_eq]

end NativeTrust.StrRepl
