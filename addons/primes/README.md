# Kernel-checked Pratt primality certificates

`Nat.Prime p` for the large field primes of zero-knowledge and cryptography libraries. Each proof
is checked by Lean's kernel, which evaluates a `Bool` certificate check with its GMP-accelerated
`Nat` arithmetic. There is no `native_decide`, no `Lean.ofReduceBool` and no `sorry`; every theorem
depends only on `propext`, `Classical.choice` and `Quot.sound`. `norm_num` reaches about 2^34;
these certificates cover 64-bit and 256-bit primes.

The add-on uses toolchain `leanprover/lean4:v4.35.0-rc3` and a Mathlib built for it; `MATHLIB_PROJECT` below
is any Lake project that depends on that Mathlib.

## Files

| file | contents |
|---|---|
| `PrattCert.lean` | the library; imports only `Mathlib.NumberTheory.LucasPrimality` |
| `PrimeCerts.lean` | certificates and theorems for the 10 primes below |
| `gen/` | `pratt.gp` (PARI/GP: factors `p - 1` recursively, finds the smallest witness), the PARI outputs, and `mkcerts.py`, which re-checks every node in Python and writes `PrimeCerts.lean` |
| `tests/` | `run.sh` runs everything below: `Axioms.lean`, `Controls.lean`, `KTime.lean`, and `KfPrime.lean` + `KfPrimeCheck.lean` (the NativeTrust test) |

`PrattCert.lean` provides:

- `powMod b e m`, binary exponentiation by structural recursion (`termination_by structural`) on a
  fuel argument. The fuel is `e`, and the loop exits once the exponent reaches 0, so it takes
  `log₂ e + 1` steps.
  - `powMod_eq : powMod b e m = b ^ e % m`, for every `m`.
- `pratt_step`: the Lucas test from Mathlib's `lucas_primality`. Its hypotheses:
  - `p - 1 = (fs.map fun qe => qe.1 ^ qe.2).prod`;
  - every `qe.1` is prime, and `2 ≤ p`;
  - `powMod a (p - 1) p = 1`;
  - `powMod a ((p - 1) / qe.1) p ≠ 1` for every `qe ∈ fs`.

  The key lemma is `exists_mem_of_prime_dvd_prod`: a prime that divides the product is one of
  the listed primes.
- `checkStep`, `checkStep_sound`: the same side conditions as one `Bool`, except the primality of
  the factors.
- `Cert`, `checkCert`, `checkTop`, `prime_of_checkTop`: a whole recursive certificate.
  - A `Cert` is a list of nodes `(p, a, [(q, e), ...])`.
  - Each factor `q` must be `2` or the prime of an earlier node.
  - One `decide +kernel` checks every node.

```lean
import PrattCert
def myCert : PrattCert.Cert := [(3, 2, [(2, 1)]), (7, 3, [(2, 1), (3, 1)])]
theorem prime_seven : Nat.Prime 7 := PrattCert.prime_of_checkTop (c := myCert) (by decide +kernel)
```

## Certified primes (all 10)

Each prime has `PrimeCerts.prime_<name> : Nat.Prime <decimal literal>` and
`PrimeCerts.fact_prime_<name> : Fact (Nat.Prime <decimal literal>)`. The primes with a closed form
also have `_pow` versions stated with that form, e.g. `prime_curve25519_p_pow : Nat.Prime (2 ^ 255 - 19)`.

| name | prime | nodes | kernel time (3 runs) |
|---|---|---|---|
| `babybear` | 2013265921 = 15·2^27 + 1 (`_pow`) | 3 | 4.4-4.6 ms |
| `koalabear` | 2130706433 = 2^31 − 2^24 + 1 (`_pow`) | 4 | 4.8-5.0 ms |
| `mersenne31` | 2147483647 = 2^31 − 1 (`_pow`) | 8 | 13-14 ms |
| `goldilocks` | 18446744069414584321 = 2^64 − 2^32 + 1 (`_pow`) | 6 | 16-17 ms |
| `bn254_r` | BN254 scalar field r (254 bits) | 46 | 0.31-0.39 s |
| `bn254_q` | BN254 base field q (254 bits) | 42 | 0.36-0.49 s |
| `secp256k1_p` | 2^256 − 2^32 − 977 (`_pow`) | 45 | 0.45-0.57 s |
| `secp256k1_n` | secp256k1 group order n (256 bits) | 45 | 0.32-0.35 s |
| `bls12_381_r` | BLS12-381 scalar field r (255 bits) | 37 | 0.24-0.29 s |
| `curve25519_p` | 2^255 − 19 (`_pow`) | 52 | 0.36-0.49 s |

How the times were measured:

- Kernel time is the minimum of 5 re-checks of the `decide +kernel` lemma (`tests/KTime.lean`),
  in each of 3 runs.
- The `_pow` forms of secp256k1 p and Curve25519 p take 0.40-0.50 s.
- All runs: shared VM at load about 100, one thread.

## Use with NativeTrust

Put the theorem in a module that the check imports. Its statement must be exactly the
proposition that the library's `native_decide` decides, so it uses the library's own constant:

```lean
import NativeTrust
import Clean.Whatever   -- has `instance : Fact (Nat.Prime pBabybear) := by native_decide`
import PrimeCerts

@[kernel_fact] theorem babybear_kf : Fact (Nat.Prime pBabybear) := PrimeCerts.fact_prime_babybear
```

The certificate theorem is accepted because `pBabybear` unfolds definitionally to the literal.

This was tested in `tests/KfPrimeCheck.lean`, against a stand-in module with
`def pBabybear : ℕ := 15 * 2 ^ 27 + 1` and the `native_decide` instance:

- the trace printed `NT kernel_fact babybearPrime._native.native_decide.ax_1 via babybear_kf`;
- `kernelize` produced `pBabybear_prime.kernel` and `pBabybear_pos.kernel`, both with
  `[propext, Classical.choice, Quot.sound]`, in about 60 ms.

## Build and compile times

```
export LEAN_PATH=$(cd "$MATHLIB_PROJECT" && lake env printenv LEAN_PATH):"$PWD"
# run in this directory
lean -o PrattCert.olean PrattCert.lean     # 1.6 s wall, 2.2 GB RSS
lean -o PrimeCerts.olean PrimeCerts.lean   # 5-9 s wall over 4 runs, 2.3 GB RSS
```

Both wall times include about 1.1 s of Mathlib import. `tests/run.sh` rebuilds both files and runs
all the checks.

## Axiom check (`tests/Axioms.lean`, output in `tests/Axioms.out`)

`#print axioms` covers all 32 theorems of `PrimeCerts` (`prime_*`, `fact_prime_*`, `*_pow`) and
4 of `PrattCert` (`pratt_step`, `checkStep_sound`, `checkCert_sound`, `prime_of_checkTop`). All 36
print exactly:

```
depends on axioms: [propext, Classical.choice, Quot.sound]
```

`PrattCert.powMod_eq` depends on `[propext, Quot.sound]`.

## Controls (`tests/Controls.lean`)

The kernel accepts the correct BabyBear certificate. It rejects 8 corrupted ones (`decide` evaluates
them to `false`):

- a wrong witness;
- a wrong exponent;
- a missing node;
- a target that is not a node;
- the base-2 pseudoprime 2047 = 23·89 with the full factorization of 2046;
- a node used before it is established;
- a composite factor 15;
- `p = 1`.

## Notes

- Trusted base: Lean's kernel, including its GMP `Nat` acceleration, and Mathlib's
  `lucas_primality`. The PARI factorizations are not trusted: the kernel checks
  `p - 1 = ∏ q ^ e` and every factor's own certificate.
- Plain `decide` also works (tested on BabyBear), but it evaluates the check in the elaborator as
  well as in the kernel. Use it on Lean versions without `decide +kernel`.
- To add a prime:
  1. In `gp -q gen/pratt.gp`, run `seen = Map(); pratt(p)` and save the `NODE` lines as
     `gen/<name>.out`. `mkcerts.py` reads every `gen/*.out`.
  2. Add a `TARGETS` line to `gen/mkcerts.py`.
  3. Run `python3 -I gen/mkcerts.py > PrimeCerts.lean`.

  The 10 trees above took under a minute in PARI.
