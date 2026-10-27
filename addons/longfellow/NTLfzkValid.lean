import NTLfzk
import Lfzk.CertifiedHahn

/-!
# `v7SigHahn_valid` (LigeroV1Rows and CertifiedV1) as kernel facts (NativeTrust add-on, longfellow)

Separate from `NTLfzk` because the mask certificate check takes about 10 minutes and 74 GB to compile.
NativeTrust splits `decide v7SigHahn.Valid` into conjuncts and the table conjunct
`integratedLocalValidBool` into points; the split unfolds `integratedLocalValidBool` before the
`NTLfzk` replacement applies, so the point checks decide `IntegratedLocalPointValid` with Pascal
binomials (deep recursion, or 46 GB). Here every expensive conjunct is its own declaration, proved with
the `Bool` forms of `NTLfzk`, and the conjunctions are registered with `@[kernel_fact]`.
-/

namespace NTLfzk
open Ligero.Examples.Grid Lfzk.LigeroV1Rows LigeroFamily

-- In this file only, the replacements of `NTLfzk` (registered there for the retry) apply to the first
-- attempt of `kdecide`, as they would with a first-attempt registration.
attribute [local kernel_replace] Nat.choose_eq_fast_choose binaryCliqueSearch_eq integratedLocalValidBool_eq

theorem v7SigHahn_ilv : v7SigHahn.certificate.integratedLocalValidBool = true := by
  rw [integratedLocalValidBool_eq]; decide +kernel

/-- `kdecide`, not `decide +kernel`: `maskStart` uses `v1Threshold`, a `Nat.sqrt`, whose well-founded
recursion the plain kernel does not unfold (NativeTrust evaluates it with fuel). -/
theorem v7SigHahn_mask : v7SigHahn.certificate.maskValid = true := by
  rw [maskValid_eq]; kdecide

theorem v7SigHahn_eps : v7SigHahn.epsRbr ≤ (1 : ℚ) / 2 ^ v7SigHahn.targetBits := by
  rw [epsRbr_eq]; decide +kernel

theorem v7SigHahn_dcc :
    SelectedMCA.DirectCliqueCondition v7SigHahn.n v7SigHahn.e v7SigHahn.g v7SigHahn.d v7SigHahn.m :=
  of_decide_eq_true (by rw [decide_dcc]; decide +kernel)

@[kernel_fact] theorem v7SigHahn_valid_kf : Lfzk.LigeroV1Rows.v7SigHahn.Valid :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, v7SigHahn_dcc,
    by decide +kernel, by decide +kernel, by decide +kernel, v7SigHahn_ilv, by decide +kernel,
    by decide +kernel, by decide +kernel, v7SigHahn_eps, v7SigHahn_mask⟩

@[kernel_fact] theorem cv1_v7SigHahn_valid_kf : Lfzk.CertifiedV1.v7SigHahn.Valid :=
  ⟨v7SigHahn_valid_kf, by kdecide, by kdecide, by unfold LigeroFamily.CoreRowsNonempty; kdecide,
    by kdecide, by kdecide, by kdecide, by kdecide⟩

end NTLfzk
