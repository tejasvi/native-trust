import NativeTrust

/-! Tests for `NativeTrust.StrLib` and `@[kernel_fold]` (Lean ≥ 4.30). Each `String` goal is blocked
without StrLib: the `String` functions below run on `String.Slice` iterators (`WellFounded.extrinsicFix`,
`Std.Shrink`); `kdecide` converts them in its retry with the retry-only replacements. -/

set_option Elab.async false

-- `String.toNat?` (`String.Slice.isNat`, `String.Slice.foldl`)
theorem strlib_toNat : "1_000".toNat? = some 1000 ∧ "12a".toNat? = none := by kdecide
#print axioms strlib_toNat

-- `String.foldl`
theorem strlib_foldl : "a b c".foldl (fun n c => if c = ' ' then n + 1 else n) 0 = 2 := by kdecide
#print axioms strlib_foldl

-- `String.replace` with `String` patterns: one character, several characters, overlapping
-- candidates, and the empty pattern (folded by `@[kernel_fold]`, replaced by `@[kernel_replace_retry]`)
theorem strlib_replace :
    "a\tb\tc".replace "\t" " " = "a b c" ∧
    "red green blue".replace "ee" "E" = "red grEn blue" ∧
    "aaaaa".replace "aa" "b" = "bba" ∧
    "abc".replace "" "k" = "kakbkck" := by kdecide
#print axioms strlib_replace

-- inside a definition (folded when NativeTrust copies `tokens`)
def tokens (s : String) : List String :=
  ((s.replace "\t" " ").splitOn " ").filter (· ≠ "")

theorem strlib_tokens : tokens "ls\t-la  x" = ["ls", "-la", "x"] := by kdecide
#print axioms strlib_tokens

-- `String.Slice.replace`
theorem strlib_slice_replace : ("x-y-z".toSlice.replace "-" "+") = "x+y+z" := by kdecide
#print axioms strlib_slice_replace

-- `String.contains` / `String.Slice.contains` with `Char` and `String` patterns
theorem strlib_contains :
    "1_000".contains '_' ∧ !"1000".contains '_' ∧ "red green".contains "een" ∧
    !"red green".contains "ner" ∧ "a-b".toSlice.contains '-' ∧ "abc".toSlice.contains "bc" := by kdecide
#print axioms strlib_contains

-- a user specialization: `@[kernel_fold]` folds `List.map Nat.succ` into `mapSucc`, which
-- `@[kernel_replace]` maps to a structural version
def mapSucc (l : List Nat) : List Nat := l.map Nat.succ
def mapSucc' : List Nat → List Nat
  | [] => []
  | x :: xs => (x + 1) :: mapSucc' xs
attribute [kernel_fold] mapSucc
@[kernel_replace] theorem mapSucc_eq : @mapSucc = @mapSucc' := by
  funext l
  induction l with
  | nil => rfl
  | cons x xs ih => simp only [mapSucc, List.map_cons, mapSucc'] at ih ⊢; rw [ih]
-- folds apply in the retry after the default routes fail; `retryRepl := true` uses them from the start
theorem strlib_fold_user : (List.range 3).map Nat.succ = [1, 2, 3] := by
  kdecide (config := { retryRepl := true })
#print axioms strlib_fold_user
