import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.Prime.Defs
import NativeTrust

/-!
# Mathlib's compiled-code replacements as NativeTrust retry replacements

Mathlib proves `@[csimp]` theorems `@f = @g` so that compiled code runs a fast `g` for a slow
reference `f`. The kernel always evaluates `f`. Two of them are what keeps facts kernel-only:

* `Nat.choose_eq_fast_choose : Nat.choose = fast_choose`: Pascal's recursion (exponential, or quadratic
  with the kernel's caches) against `descFactorial n k / k !`;
* `Nat.decidablePrime_csimp : @decidablePrime = @decidablePrime'`: the linear scan `∀ m < p` against
  trial division up to the least factor (`minFac`).

`fast_choose` is `descFactorial n k / k !`, and the kernel evaluates `descFactorial` and `factorial` by
linear recursion (`k` nested calls: "deep recursion" for `k` in the thousands), so their binary-splitting
replacements are registered too.

They are registered with `@[kernel_replace_retry]`: NativeTrust uses them only in the retry after
the default attempts fail, so a fact that converts without them converts exactly as before. They are
theorems of Mathlib (from the standard axioms), so they add no trust. Import this module (driver:
`--extra-import NTMathlibCsimp`) in projects that use Mathlib.
-/

attribute [kernel_replace_retry] Nat.choose_eq_fast_choose
attribute [kernel_replace_retry] Nat.decidablePrime_csimp
attribute [kernel_replace_retry] Nat.descFactorial_eq_descFactorialBinary
attribute [kernel_replace_retry] Nat.ascFactorial_eq_ascFactorialBinary
attribute [kernel_replace_retry] Nat.factorial_eq_factorialBinarySplitting
