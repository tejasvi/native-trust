import PrimeCerts
open Lean Elab Command

/-- Kernel time of re-checking the `decide +kernel` auxiliary lemma(s) used by theorem `id`
(min over `n` runs, synchronous `Environment.addDeclCore`). -/
elab "#ktime " id:ident n:num : command => do
  let env ← getEnv
  let some (.thmInfo info) := env.find? id.getId | throwError "not a theorem"
  let auxs := info.value.getUsedConstants.filter fun c => (c.toString.splitOn "_proof").length > 1
  for aux in auxs do
    let some (.thmInfo ai) := env.find? aux | throwError "aux not a theorem"
    let mut best : Nat := 1000000000000
    for i in [0:n.getNat] do
      let decl := Declaration.thmDecl { ai with name := aux ++ Name.mkSimple s!"ktime{i}" }
      let t0 ← IO.monoNanosNow
      match env.addDeclCore 0 100000 decl none with
      | .ok _ => pure ()
      | .error _ => throwError "kernel rejected {aux}"
      let t1 ← IO.monoNanosNow
      best := min best (t1 - t0)
    logInfo m!"{id.getId} via {aux}: kernel {best / 1000} us (min of {n.getNat})"

#ktime PrimeCerts.prime_babybear 5
#ktime PrimeCerts.prime_koalabear 5
#ktime PrimeCerts.prime_mersenne31 5
#ktime PrimeCerts.prime_goldilocks 5
#ktime PrimeCerts.prime_bn254_r 5
#ktime PrimeCerts.prime_bn254_q 5
#ktime PrimeCerts.prime_secp256k1_p 5
#ktime PrimeCerts.prime_secp256k1_n 5
#ktime PrimeCerts.prime_bls12_381_r 5
#ktime PrimeCerts.prime_curve25519_p 5
#ktime PrimeCerts.prime_secp256k1_p_pow 5
#ktime PrimeCerts.prime_curve25519_p_pow 5
