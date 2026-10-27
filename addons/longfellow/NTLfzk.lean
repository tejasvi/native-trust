import NativeTrust
import examples.Ligero.Certificate
import Lfzk.LigeroV1Rows
import Lfzk.LigeroV1RowsHahn

/-!
# Kernel-friendly forms of longfellow's selected-MCA checks (NativeTrust add-on, longfellow)

`Nat.choose` evaluates by Pascal's recursion, so the kernel recurses about `n` levels for
`Nat.choose n k`. Longfellow's `SelectedMCA.DirectCliqueCondition` takes `m.choose 2` and `m.choose 3`
with `m ≈ 8.7·10⁶` (and `balanced_choose_three` takes `lo.choose 3` with `lo ≈ 4.6·10⁶`):
"(kernel) deep recursion detected".

Mathlib's `Nat.choose_eq_fast_choose` (`descFactorial n k / k !`, recursion depth `k`) fixes the
occurrences that the evaluation reaches through definitions of values. It does not reach
`binaryCliqueSearch` and `Certificate.integratedLocalValidBool`: their bodies decide the `Prop`s
`DirectCliqueCondition` and `IntegratedLocalPointValid`, and NativeTrust cannot copy a definition whose
copy changes a type (the decided proposition). This module proves `Bool` versions of both functions
equal to the originals; with the equations registered, NativeTrust evaluates the `Bool` versions.

The replacements are registered with `@[kernel_replace_retry]`: NativeTrust uses them only after the
default attempts fail, so a fact that converts without this module converts exactly as before (a
first-attempt registration slowed previously proved longfellow facts whose project instances cannot be
copied). The cost is the failed default attempt (about 190 s and 30 GB on these facts). The
replacements are theorems (standard axioms), so they add no trust. Import with
`--extra-import NTLfzk --extra-path <dir>`.
-/

namespace NTLfzk
open Ligero.Examples.Grid

attribute [kernel_replace_retry] Nat.choose_eq_fast_choose

/-- `SelectedMCA.simpleCliqueUpperNat` with `Nat.fast_choose`. -/
def simpleCliqueUpperK (m R : ℕ) : ℕ := (R - 2) * Nat.fast_choose m 2 / 3

/-- `AffineAgreement.Internal.balanced_choose_three` with `Nat.fast_choose`. -/
def balancedChooseThreeK (n total : ℕ) : ℕ :=
  (n - total % n) * Nat.fast_choose (total / n) 3 + total % n * Nat.fast_choose (total / n + 1) 3

/-- `decide (SelectedMCA.DirectCliqueCondition n e g d m)` as a `Bool` with `Nat.fast_choose`. -/
def dccB (n e g d m : ℕ) : Bool :=
  decide (3 ≤ m) && decide (n - d < n - e) &&
    decide (simpleCliqueUpperK m (n / (g + 1)) * ((n - e) - (n - d)) + Nat.fast_choose m 3 * (n - d) <
      balancedChooseThreeK n (m * (n - e)))

theorem decide_dcc (n e g d m : ℕ) :
    decide (SelectedMCA.DirectCliqueCondition n e g d m) = dccB n e g d m := by
  simp only [dccB, SelectedMCA.DirectCliqueCondition, simpleCliqueUpperK, balancedChooseThreeK,
    SelectedMCA.simpleCliqueUpperNat, SelectedMCA.directLineOccupancyBound,
    AffineAgreement.Internal.balanced_choose_three, ← Nat.choose_eq_fast_choose, Bool.decide_and,
    Bool.and_assoc]

/-- `decide` with any instance equals a `Bool` that reflects the proposition. -/
theorem decide_eq_of_iff' {p : Prop} (i : Decidable p) {b : Bool} (h : p ↔ b = true) : @decide p i = b :=
  Bool.eq_iff_iff.mpr ⟨fun hd => h.mp (@of_decide_eq_true p i hd), fun hb => @decide_eq_true p i (h.mpr hb)⟩

/-- `binaryCliqueSearch` deciding the clique condition with `dccB`. -/
def binaryCliqueSearchK (n radius g d : ℕ) : ℕ → ℕ → ℕ → ℕ
  | 0, _lo, hi => hi
  | fuel + 1, lo, hi =>
      if lo < hi then
        if dccB n radius g d ((lo + hi) / 2) then
          binaryCliqueSearchK n radius g d fuel lo ((lo + hi) / 2)
        else
          binaryCliqueSearchK n radius g d fuel ((lo + hi) / 2 + 1) hi
      else hi

@[kernel_replace_retry] theorem binaryCliqueSearch_eq : @binaryCliqueSearch = @binaryCliqueSearchK := by
  funext n radius g d fuel
  induction fuel with
  | zero => funext lo hi; rfl
  | succ fuel ih =>
    funext lo hi
    simp only [binaryCliqueSearch, binaryCliqueSearchK, ih, decide_dcc]

/-- `Certificate.integratedLocalM` with `binaryCliqueSearchK`. -/
def integratedLocalMK (c : Certificate) (a : ℕ) : ℕ :=
  if 3 * (c.n - a) < c.d then c.m
  else binaryCliqueSearchK c.n (c.n - a) c.g c.d 64 3 (max c.m c.refinedLocalM)

/-- `decide (c.IntegratedLocalPointValid a)` as a `Bool`. -/
def integratedLocalPointValidB (c : Certificate) (a : ℕ) : Bool :=
  dccB c.n (c.n - a) c.g c.d (integratedLocalMK c a) &&
    (decide (3 * (c.n - a) < c.d) || !dccB c.n (c.n - a) c.g c.d (integratedLocalMK c a - 1))

/-- `Certificate.integratedLocalValidBool` with `integratedLocalPointValidB`. -/
def integratedLocalValidBoolK (c : Certificate) : Bool :=
  (List.range (c.n + 1)).all fun a ↦
    if c.n - c.e ≤ a then integratedLocalPointValidB c a else true

theorem integratedLocalM_eq (c : Certificate) (a : ℕ) : c.integratedLocalM a = integratedLocalMK c a := by
  simp only [Certificate.integratedLocalM, integratedLocalMK, binaryCliqueSearch_eq]

@[kernel_replace_retry] theorem integratedLocalValidBool_eq :
    @Certificate.integratedLocalValidBool = @integratedLocalValidBoolK := by
  funext c
  unfold Certificate.integratedLocalValidBool integratedLocalValidBoolK
  congr 1
  funext a
  split
  · apply decide_eq_of_iff'
    simp only [Certificate.IntegratedLocalPointValid, integratedLocalPointValidB, integratedLocalM_eq,
      Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq, ← decide_dcc]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨h1, ?_⟩
      by_cases h : 3 * (c.n - a) < c.d
      · exact Or.inl h
      · exact Or.inr (by simpa using h2 h)
    · rintro ⟨h1, h2⟩
      refine ⟨h1, fun h => ?_⟩
      rcases h2 with h2 | h2
      · exact absurd h2 h
      · simpa using h2
  · rfl

/-! ## `LigeroV1Rows.Row.Sharp`

`Row.Sharp` (`¬ epsRbr ≤ 2^-(target+1)`) is decided by the project's instance, whose body decides a
proposition about `epsRbr`; NativeTrust cannot copy that instance (the copy would change its type),
so the replacements above do not reach the `binaryCliqueSearch` inside `epsRbr`. `epsRbrK`/`sharpB`
evaluate `Sharp` with `binaryCliqueSearchK`; the fact itself is proved from `sharpB` below. -/

open Lfzk.LigeroV1Rows LigeroFamily

/-- `Certificate.integratedLocalLineBound` with `binaryCliqueSearchK`. -/
def integratedLocalLineBoundK (c : Certificate) (a : ℕ) : ℕ :=
  SelectedMCA.directLineFailureBound (integratedLocalMK c a)

theorem integratedLocalLineBound_eq (c : Certificate) :
    c.integratedLocalLineBound = integratedLocalLineBoundK c := by
  funext a
  simp only [Certificate.integratedLocalLineBound, integratedLocalLineBoundK, integratedLocalM_eq]

/-- `Row.epsRbr` with `integratedLocalLineBoundK` in the failure profile. -/
def epsRbrK (row : Row) : ℚ :=
  (row.listBound : ℚ) * (row.cover +
    ((SchemeSelectedMCA.selectedMCAOptimizedIntegratedFailureProfile row.fieldSize row.n row.e row.g row.d
        row.certificate.lineBound (integratedLocalLineBoundK row.certificate)).labelsAtLeast
        (row.failureThreshold + 1) : ℚ) / (row.certificate.optimizedFailureDenominator : ℚ) +
    row.arith)

theorem epsRbr_eq (row : Row) : row.epsRbr = epsRbrK row := by
  simp only [Row.epsRbr, epsRbrK, Row.fail, Row.failureProfileAt, integratedLocalLineBound_eq]

/-- `decide row.Sharp` as a `Bool` with `epsRbrK`. -/
def sharpB (row : Row) : Bool := !decide (epsRbrK row ≤ (1 : ℚ) / 2 ^ (row.targetBits + 1))

theorem sharpB_iff (row : Row) : sharpB row = true ↔ row.Sharp := by
  simp only [sharpB, Row.Sharp, epsRbr_eq, Bool.not_eq_true', decide_eq_false_iff_not]


/-! ## `v7SigHahn_sharp` as a kernel fact

NativeTrust's evaluation of `decide v7SigHahn.Sharp` goes through the project's instance and ends in
deep recursion (a replacement of the instance through `Subsingleton` is not used: the instance is
unfolded before replacements apply). The `Bool` check `sharpB` evaluates in the kernel in
about 25 s, so the fact is proved here and registered with `@[kernel_fact]`. -/

@[kernel_fact] theorem v7SigHahn_sharp_kf : Lfzk.LigeroV1Rows.v7SigHahn.Sharp :=
  (sharpB_iff _).mp (by decide +kernel)

/-! ## `fast_choose` versions of the Hahn/Delsarte mask certificate (used by `NTLfzkValid`) -/

open Finset in
/-- `CodingTheory.HahnDelsarte.hahnWeight` with `Nat.fast_choose`. -/
def hahnWeightK (n w k x : ℕ) : ℚ :=
  (-1) ^ x * ((Nat.fast_choose ((n + x) - (w + k)) x : ℕ) : ℚ) / ((Nat.fast_choose w x : ℕ) : ℚ)

open Finset in
/-- `CodingTheory.HahnDelsarte.hahnKernel` with `Nat.fast_choose`. -/
def hahnKernelK (n w k t : ℕ) : ℚ :=
  ∑ i ∈ range (k + 1), hahnWeightK n w k i *
    ∑ a ∈ range (i + 1), ((Nat.fast_choose t a * Nat.fast_choose (w - t) (i - a) : ℕ) : ℚ) *
      ∑ c ∈ range (k - i + 1),
        ((Nat.fast_choose (w - t) c * Nat.fast_choose (n + t - 2 * w) (k - i - c) : ℕ) : ℚ) *
          hahnWeightK n w k (a + c)

open Finset in
/-- `CodingTheory.HahnDelsarte.certificatePolynomial` with `hahnKernelK`. -/
def certificatePolynomialK (n w : ℕ) (coeffs : List ℕ) (t : ℕ) : ℚ :=
  (coeffs.headD 0 : ℚ) +
    ∑ k ∈ Icc 1 (coeffs.length - 1), (coeffs.getD k 0 : ℚ) * hahnKernelK n w k t

/-- `CodingTheory.HahnDelsarte.certificateValid` with `certificatePolynomialK`. -/
def certificateValidK (n w lam : ℕ) (coeffs : List ℕ) : Bool :=
  decide (0 < coeffs.headD 0) &&
    (List.range (lam + 1)).all fun t ↦
      decide (n + t < 2 * w) || decide (certificatePolynomialK n w coeffs t ≤ 0)

theorem certificateValid_eq :
    @CodingTheory.HahnDelsarte.certificateValid = @certificateValidK := by
  funext n w lam coeffs
  simp only [CodingTheory.HahnDelsarte.certificateValid, certificateValidK,
    CodingTheory.HahnDelsarte.certificatePolynomial, certificatePolynomialK,
    CodingTheory.HahnDelsarte.hahnKernel, hahnKernelK, CodingTheory.HahnDelsarte.hahnWeight,
    hahnWeightK, Nat.choose_eq_fast_choose]

/-- `Certificate.maskValid` with `certificateValidK`. -/
def maskValidK (c : Certificate) : Bool :=
  decide (c.maskStart ≤ c.v1Threshold) && decide (2 * c.k - 1 < c.maskStart) &&
    (decide (c.v1Threshold ≤ c.maskStart) || certificateValidK c.n c.maskStart (2 * c.k - 1) c.hahnMask)

theorem maskValid_eq (c : Certificate) : c.maskValid = maskValidK c := by
  simp only [Certificate.maskValid, maskValidK, certificateValid_eq]

end NTLfzk
