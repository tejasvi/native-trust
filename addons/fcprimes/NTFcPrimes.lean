import PrattCert
import NativeTrust

/-!
# Pratt certificates for formal-conjectures' Erdős 313 primes (NativeTrust add-on)

`erdos_313.variants.exists_at_least_eight_primary_pseudoperfect` proves `Nat.Prime p` by `native_decide`
for the prime factors of the eighth primary pseudoperfect number. The kernel cannot run Mathlib's
`Nat.Prime` decision procedure on the large ones in time (with v13's `csimp := true`, trial division up
to `√p`: 47059 and 2217342227 convert, 1729101023519 does not in 900 s).

These theorems prove them from Pratt certificates (`PrattCert`, a copy of `primes/PrattCert.lean`): one
`decide +kernel` of a `Bool` certificate check with GMP-accelerated arithmetic. `@[kernel_fact]` makes
NativeTrust use them for the native facts `decide (Nat.Prime p) = true`. Certificates generated and
re-checked by `pratt_gen.py`. Import this module in the kernel supplement of formal-conjectures
(driver: `--extra-import NTFcPrimes --extra-path <dir>`).
-/

namespace NTFcPrimes

def cert47059 : PrattCert.Cert :=
  [(3, 2, [(2, 1)]), (5, 2, [(2, 2)]), (11, 2, [(2, 1), (5, 1)]), (23, 5, [(2, 1), (11, 1)]),
   (31, 3, [(2, 1), (3, 1), (5, 1)]), (47059, 2, [(2, 1), (3, 1), (11, 1), (23, 1), (31, 1)])]

def cert2217342227 : PrattCert.Cert :=
  [(5, 2, [(2, 2)]), (11, 2, [(2, 1), (5, 1)]), (3, 2, [(2, 1)]), (7, 3, [(2, 1), (3, 1)]),
   (29, 2, [(2, 2), (7, 1)]), (19, 2, [(2, 1), (3, 2)]), (191, 19, [(2, 1), (5, 1), (19, 1)]),
   (383, 5, [(2, 1), (191, 1)]), (4597, 5, [(2, 2), (3, 1), (383, 1)]),
   (27583, 3, [(2, 1), (3, 1), (4597, 1)]),
   (100788283, 7, [(2, 1), (3, 2), (7, 1), (29, 1), (27583, 1)]),
   (2217342227, 2, [(2, 1), (11, 1), (100788283, 1)])]

def cert1729101023519 : PrattCert.Cert :=
  [(5, 2, [(2, 2)]), (11, 2, [(2, 1), (5, 1)]), (3, 2, [(2, 1)]), (7, 3, [(2, 1), (3, 1)]),
   (29, 2, [(2, 2), (7, 1)]), (23, 5, [(2, 1), (11, 1)]), (461, 2, [(2, 2), (5, 1), (23, 1)]),
   (22129, 19, [(2, 4), (3, 1), (461, 1)]), (398323, 2, [(2, 1), (3, 2), (22129, 1)]),
   (78595501069, 2, [(2, 2), (3, 5), (7, 1), (29, 1), (398323, 1)]),
   (1729101023519, 11, [(2, 1), (11, 1), (78595501069, 1)])]

@[kernel_fact] theorem prime_47059 : Nat.Prime 47059 :=
  PrattCert.prime_of_checkTop (c := cert47059) (by decide +kernel)

@[kernel_fact] theorem prime_2217342227 : Nat.Prime 2217342227 :=
  PrattCert.prime_of_checkTop (c := cert2217342227) (by decide +kernel)

@[kernel_fact] theorem prime_1729101023519 : Nat.Prime 1729101023519 :=
  PrattCert.prime_of_checkTop (c := cert1729101023519) (by decide +kernel)

end NTFcPrimes
