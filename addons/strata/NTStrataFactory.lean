import NativeTrust
import Strata.DL.Lambda.Factory

/-!
# Kernel replacements for Strata's `Lambda.Factory` lookups (add-on, package-specific)

A `Factory` keeps its functions in an array (`toArray`) and, for constant-time lookup, a
`Std.HashMap String Nat` from names to indices (`nameMap`, private), with invariants: every array element's
name maps to its index, and every key maps to a valid index of an element with that name. Membership
(`name ∈ f.nameMap`) and `Factory.get` read the hash map, and `String.hash` has no kernel definition, so
the kernel cannot evaluate them (`StrataTest.DL.Lambda.Denote.Tautologies`: 34 facts).

By the invariants both are determined by the array: `name ∈ f` iff some element has that name, and
`f.get name p` is the first element with that name (names are unique). `instMemDecidable_eq` and
`get_eq`, registered with `@[kernel_replace_retry]`, let the retry evaluate these array versions instead.
The hash map itself is then never read, so it is never computed: `Factory.push` stores it in a field that
evaluation does not project.

`nameMap` and the invariant fields are private to Strata's module; they are aliased here (`run_meta`,
the same kernel constants).
-/

namespace NTStrata
open Lean Meta Lambda

open Lean Meta in
run_meta do
  let priv (n : Name) : Name := (Name.mkNum (`_private ++ `Strata.DL.Lambda.Factory) 0) ++ n
  for (a, n) in [(`NTStrata.nameMapP, `Lambda.Factory.nameMap), (`NTStrata.toArrayDefinedP, `Lambda.Factory.toArrayDefined),
      (`NTStrata.nameMapValidP, `Lambda.Factory.nameMapValid), (`NTStrata.nameMapConsistentP, `Lambda.Factory.nameMapConsistent)] do
    let p := priv n
    let some ci := (← getEnv).find? p | throwError "NTStrata: no constant {p}"
    let decl := match ci with
      | .thmInfo _ => Declaration.thmDecl { name := a, levelParams := ci.levelParams, type := ci.type, value := mkConst p (ci.levelParams.map mkLevelParam) }
      | _ => Declaration.defnDecl { name := a, levelParams := ci.levelParams, type := ci.type, value := mkConst p (ci.levelParams.map mkLevelParam), hints := .abbrev, safety := .safe }
    addDecl decl

variable {T : LExprParams}

/-- Is some element of the array named `name`? -/
def memL (f : Factory T) (name : String) : Bool := f.toArray.any (fun fn => fn.name.name == name)

theorem mem_iff_exists (f : Factory T) (name : String) :
    f.mem name ↔ ∃ i : Fin f.toArray.size, f.toArray[i].name.name = name := by
  constructor
  · intro p
    have hv := nameMapValidP f p
    exact ⟨⟨_, hv⟩, nameMapConsistentP f p⟩
  · rintro ⟨i, hi⟩
    have h := toArrayDefinedP f i
    rw [hi] at h
    show name ∈ nameMapP f
    exact Std.HashMap.mem_iff_isSome_getElem?.2 (by rw [show (nameMapP f)[name]? = some ↑i from h]; rfl)

theorem mem_iff_memL (f : Factory T) (name : String) : f.mem name ↔ memL f name = true := by
  rw [mem_iff_exists, memL, Array.any_eq_true]
  constructor
  · rintro ⟨⟨i, hi⟩, h⟩
    exact ⟨i, hi, by simpa using h⟩
  · rintro ⟨i, hi, h⟩
    exact ⟨⟨i, hi⟩, by simpa using h⟩

/-- Membership decided by the array. -/
def instMemDecidableL (f : Factory T) (name : String) : Decidable (f.mem name) :=
  decidable_of_iff _ (mem_iff_memL f name).symm

@[kernel_replace_retry] theorem instMemDecidable_eq :
    @Factory.instMemDecidable = @instMemDecidableL := by
  funext T f name
  exact Subsingleton.elim _ _

/-- Names are unique in the array. -/
theorem index_unique (f : Factory T) (i j : Fin f.toArray.size)
    (h : f.toArray[i].name.name = f.toArray[j].name.name) : i = j := by
  have hi := toArrayDefinedP f i
  have hj := toArrayDefinedP f j
  rw [h] at hi
  rw [hi] at hj
  exact Fin.ext (Option.some.inj hj)

theorem find?_isSome (f : Factory T) (name : String) (p : name ∈ f) :
    (f.toArray.find? (fun fn => fn.name.name == name)).isSome := by
  obtain ⟨i, hi⟩ := (mem_iff_exists f name).1 p
  rw [Array.find?_isSome]
  exact ⟨f.toArray[i], Array.getElem_mem _, by simpa using hi⟩

/-- The element named `name`, found in the array. -/
def getL (f : Factory T) (name : String) (p : name ∈ f) : LFunc T :=
  (f.toArray.find? (fun fn => fn.name.name == name)).get (find?_isSome f name p)

@[kernel_replace_retry] theorem get_eq : @Factory.get = @getL := by
  funext T f name p
  -- `f.get name p` is `f.toArray[nameMap[name]]`, an element named `name`
  have hp : name ∈ nameMapP f := p
  have hv : (nameMapP f)[name]'hp < f.toArray.size := nameMapValidP f hp
  have hc : (f.toArray[(nameMapP f)[name]'hp]'hv).name.name = name := nameMapConsistentP f hp
  show f.toArray[(nameMapP f)[name]'hp]'hv = getL f name p
  -- `find?` returns an element named `name`, which by uniqueness is that one
  have hfind : f.toArray.find? (fun fn => fn.name.name == name) = some (f.toArray[(nameMapP f)[name]'hp]'hv) := by
    obtain ⟨y, hy⟩ := Option.isSome_iff_exists.1 (find?_isSome f name p)
    rw [hy]
    have hyn : y.name.name = name := by simpa using Array.find?_some hy
    obtain ⟨k, hk, rfl⟩ := Array.mem_iff_getElem.1 (Array.mem_of_find?_eq_some hy)
    have hidx := index_unique f ⟨k, hk⟩ ⟨_, hv⟩ (by
      show f.toArray[k].name.name = (f.toArray[(nameMapP f)[name]'hp]'hv).name.name
      rw [hyn, hc])
    simp only [Fin.mk.injEq] at hidx
    simp only [hidx]
  obtain ⟨_, hget⟩ := Option.eq_some_iff_get_eq.1 hfind
  exact hget.symm

end NTStrata

#print axioms NTStrata.instMemDecidable_eq
#print axioms NTStrata.get_eq
