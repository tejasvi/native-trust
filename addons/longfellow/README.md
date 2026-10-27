# longfellow-zk add-on

Opt-in modules for longfellow-zk's facts that evaluate Mathlib's `Nat.choose` by Pascal's recursion: the
kernel recurses about `n` levels for `Nat.choose n k`, and the selected-MCA checks take binomial
coefficients of numbers near 8.7 million ("(kernel) deep recursion detected"). The add-on uses toolchain
`v4.31.0`, the version the package pins.

| file | contents |
|---|---|
| `NTLfzk.lean` | `Nat.choose_eq_fast_choose` registered as a replacement; versions of `binaryCliqueSearch` and `integratedLocalValidBool` with `fast_choose`, proved equal to the originals and registered as replacements; `Bool` forms of `DirectCliqueCondition`, `Row.Sharp` and the Hahn/Delsarte certificate check, each proved equivalent to the original; `v7SigHahn.Sharp` proved and registered with `@[kernel_fact]` |
| `NTLfzkValid.lean` | the conjuncts of `LigeroV1Rows.v7SigHahn.Valid` and `CertifiedV1.v7SigHahn.Valid` proved as separate declarations; both conjunctions registered with `@[kernel_fact]` |

The replacements are registered with `@[kernel_replace_retry]`, so a fact that converts without these
modules converts exactly as before. Import them only for the facts that need them.

To use the add-on, compile `NTLfzk.lean` and then `NTLfzkValid.lean` to oleans in the package's environment,
that is, run `lean -o` with `LEAN_PATH` set to a NativeTrust build for v4.31.0, the package's `lake env` path and
this directory. Then run the driver with `--extra-path <this directory> --extra-import NTLfzk --extra-import NTLfzkValid`.
