import Clean.Utils.Primes
import Mathlib.Tactic.NormNum.Prime
import NativeTrust

/-! Remedy experiment for Verified-zkEVM/clean: kernel-checked primality proofs (`norm_num`) for the
`Fact (Nat.Prime p)` instances that the package proves by `native_decide`. Registered with
`@[kernel_fact]`, they replace those native facts; every downstream fact that mentions the field
`F p` depends on them. -/

-- the kernel checks `norm_num`'s primality proofs with a deep (non-tail) recursion
set_option maxRecDepth 1000000

@[kernel_fact] theorem kf_p1009 : Fact (p1009.Prime) := ⟨by show Nat.Prime 1009; norm_num⟩
@[kernel_fact] theorem kf_pBabybear : Fact (pBabybear.Prime) := ⟨by show Nat.Prime 2013265921; norm_num⟩
@[kernel_fact] theorem kf_pMersenne : Fact (pMersenne.Prime) := ⟨by show Nat.Prime 2147483647; norm_num⟩
@[kernel_fact] theorem kf_pSHA256 : Fact (pSHA256.Prime) := ⟨by show Nat.Prime 17179869209; norm_num⟩

#print axioms kf_pSHA256
