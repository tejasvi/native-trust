import PrattCert

/-!
# Kernel-checked primality of field primes used by zero-knowledge and cryptography libraries

Pratt certificates (`PrattCert.Cert`), each checked by one `decide +kernel`: the kernel evaluates
`PrattCert.checkTop p cert` with GMP-accelerated `Nat` arithmetic. Each certificate is
self-contained: every odd prime factor of `q - 1` for a node `q` has its own node, down to `2`.

For each prime: `prime_<name> : Nat.Prime <literal>` and
`fact_prime_<name> : Fact (Nat.Prime <literal>)`; where the prime has a standard closed form, also
`prime_<name>_pow` and `fact_prime_<name>_pow`, stated with that form (e.g.
`Nat.Prime (2 ^ 255 - 19)`).

The certificates were generated with PARI/GP (`factor`, smallest Lucas witness) and are verified
here only by the kernel; no factorization is trusted.
-/

namespace PrimeCerts

open PrattCert

