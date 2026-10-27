import NativeTrust

/-!
# The platform case split (`proveTrueByKernelPlatform`), without Mathlib

`USize` arithmetic depends on `System.Platform.numBits`, which the kernel cannot evaluate
(`System.Platform.getNumBits` is opaque), and so does `Std.HashMap`/`Std.HashSet` code. The retry evaluates such
a term at `numBits = 32` and at `numBits = 64` and combines the two cases by `System.Platform.numBits_eq`.

* `setFacts`, `mapFacts`: hash-set and hash-map queries, the same at both word sizes: they convert, and only
  with the retry;
* `wordSizeKnown`, `wrapsMod`: the same at both word sizes, so they convert with the retry;
* `wordSize64`, `usizeSize64`, `noWrap`: their counterparts that hold on a 64-bit platform but not on a 32-bit
  one. They are true natively here, but the logic does not know the word size, so they must not convert;
* `usizeMax`: the same at both word sizes, but with the hypothesis `numBits = v` free the kernel computes
  arithmetic on numbers near `2 ^ 32` step by step (on 4.35 and later; earlier toolchains cannot copy
  `USize.decEq` for the case split at all). The case split must fail within its bound, not run on;
* `bigSet`: converts, and fails with its reason when the hard limit `platformHeartbeats` is set too low.
-/

namespace PlatformCasesTest

/-- A hash set built from a list, then queried. -/
def setFacts : Bool :=
  let s : Std.HashSet Nat := [3, 5, 8, 13].foldl (fun s n => s.insert n) {}
  s.contains 5 && !s.contains 4 && s.size == 4

/-- A hash map with an overwritten key. -/
def mapFacts : Bool :=
  let m : Std.HashMap Nat String := (({} : Std.HashMap Nat String).insert 1 "a").insert 2 "b" |>.insert 1 "c"
  m[1]? == some "c" && m[2]? == some "b" && m.size == 2

/-- The word size is 32 or 64. -/
def wordSizeKnown : Bool := decide (System.Platform.numBits = 32 ∨ System.Platform.numBits = 64)

/-- Depends on the word size. -/
def wordSize64 : Bool := decide (System.Platform.numBits = 64)

/-- Depends on the word size, through `USize.size`. -/
def usizeSize64 : Bool := decide (USize.size = 18446744073709551616)

/-- `2 ^ 32` as a `USize`, reduced mod `2 ^ 32`: `0` at both word sizes. -/
def wrapsMod : Bool := (USize.ofNat 4294967296).toNat % 4294967296 == 0

/-- Depends on the word size: `2 ^ 32` as a `USize` is `0` on a 32-bit platform. -/
def noWrap : Bool := (USize.ofNat 4294967296).toNat != 0

/-- `2 ^ 64 - 1` and `0 - 1` agree at both word sizes (`2 ^ 64 - 1` mod `2 ^ 32` is `2 ^ 32 - 1`). -/
def usizeMax : Bool := (0 : USize) - 1 == USize.ofNat 18446744073709551615

/-- A larger hash set (resizes on the way). -/
def bigSet : Bool := ((List.range 300).foldl (fun s n => s.insert n) (∅ : Std.HashSet Nat)).size == 300

-- the word-size-dependent ones hold natively on this (64-bit) machine
#eval (wordSize64, usizeSize64, noWrap)

/-! ## Checks -/

open Lean Meta NativeTrust in
def check (c : Name) (platform : Bool) : MetaM String := do
  let name := (`_platformCasesTest ++ c).appendIndexAfter (if platform then 1 else 0)
  try
    let r ← proveTrueByKernel (mkConst c) name [] { native := false, platformCases := platform }
    return s!"proved; axioms {(← collectAxioms r.thm).toList}"
  catch _ => return "failed"

-- `usizeMax` spends its kernel budget, which counts against the command's heartbeats too
set_option maxHeartbeats 0 in
open Lean Meta NativeTrust in
#eval show MetaM Unit from do
  for c in [``setFacts, ``mapFacts, ``wordSizeKnown, ``wrapsMod, ``wordSize64, ``usizeSize64, ``noWrap,
      ``usizeMax] do
    IO.println s!"{c}: platformCases=false {← check c false}; platformCases=true {← check c true}"

-- the hard limit on every evaluation of the case split (here without the pre-check)
set_option maxHeartbeats 0 in
open Lean Meta NativeTrust in
#eval show MetaM Unit from do
  IO.println s!"bigSet: default {← check ``bigSet true}"
  let r ← try
      let cfg : KernelConfig := { native := false, platformProbeHeartbeats := 0, platformHeartbeats := 10 }
      let _ ← proveTrueByKernel (mkConst ``bigSet) `_platformCasesTest_hard [] cfg
      pure "proved"
    catch e => do
      let m ← e.toMessageData.toString
      pure (if (m.splitOn "thousand heartbeats (`platformHeartbeats`").length > 1 then
        "failed: did not finish within 10 thousand heartbeats (`platformHeartbeats`)" else "failed (another reason)")
  IO.println s!"bigSet with platformHeartbeats := 10: {r}"

/-! ## `native_decide` facts and `kernelize`

A fact whose truth depends on the word size stays native: `kernelize` fails, says why, and adds nothing (the
theorem keeps its axioms, and no `.kernel` theorem appears). A hash-map fact converts. -/

theorem ndWord : System.Platform.numBits = 64 := by native_decide

theorem ndSize : USize.size = 18446744073709551616 := by native_decide

theorem ndMap : ((∅ : Std.HashMap Nat Nat).insert 1 2).size = 1 := by native_decide

open Lean Elab Term NativeTrust in
#eval show TermElabM Unit from do
  for c in [``ndWord, ``ndSize, ``ndMap] do
    let before ← collectAxioms c
    let r ← kernelizeOne { native := false } c (c ++ `kernel) (soft := true)
    let verdict ← if r.startsWith "OK" then pure s!"OK; axioms {(← collectAxioms (c ++ `kernel)).toList}"
      else if (r.splitOn "at numBits = 32 the term evaluates to `false`").length > 1 then
        pure "FAILED: at numBits = 32 the term evaluates to `false`"
      else pure "FAILED (another reason)"
    let same := (← collectAxioms c) == before
    IO.println s!"kernelize {c}: {verdict}; {c} keeps its axioms: {same}; {c ++ `kernel} exists: {(← getEnv).contains (c ++ `kernel)}"

/-! The user-facing tactic. -/

theorem s1 : setFacts = true := by kdecide

theorem m1 : mapFacts = true := by kdecide

#print axioms s1
#print axioms m1

end PlatformCasesTest
