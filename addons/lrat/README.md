# Bitmask LRAT checker for `bv_decide` facts (core's bit-blaster)

A kernel-oriented LRAT (RUP) checker on natural-number bitmasks, applied to `bv_decide` facts
through a kernel-evaluable copy of core's bit-blasting pipeline. This is the earlier of the two
`bv_decide` routes; `../bvs/` has the later one, with its own bit-blaster written for the kernel,
which scales to much larger CNFs.

| file | contents |
|---|---|
| `LratBits.lean` | the checker: clauses and partial assignments as pairs of `Nat` bitmasks, unit propagation with `Nat.land`/`lor`/`xor`/shifts (GMP in the kernel), clauses in a binary trie; each hint carries the variable it makes unit, checked by the kernel |
| `LratBitsSound.lean` | `LratBits.unsat_list_of_checkBits`: acceptance implies that the clause list is unsatisfiable (core lemmas only) |
| `adapter-4.31/LratAdapter.lean`, `adapter-4.35/LratAdapter.lean` | `LratBits.unsat_of_checkBits`, the same for core's `Std.Sat.CNF.Unsat`; one file for Lean 4.31-4.34 and one for Lean 4.35 and later (core changed `CNF.Clause`) |
| `BvdKC.lean` | a copy of core's `bv_decide` soundness chain with the opaque `mixHash` and `System.Platform.getNumBits` replaced by ordinary definitions, re-checked by the kernel |
| `BitsKernel.lean` | the driver (`kb_check t`, `kb_kernelize t`): compiled code parses the certificate (untrusted), the kernel evaluates the checker; `LratBits.kb_unsat` gives `BVLogicalExpr.Unsat` |
| `AxCheck.lean` | prints the axioms of the three soundness theorems |

## Build

The modules are plain Lean files compiled one at a time, with the NativeTrust library (built from
the top directory of this artifact with `lake build`, same toolchain) on `LEAN_PATH`. From this
directory, for Lean 4.35:

```
NT_LIB=../../.lake/build/lib/lean          # NativeTrust's build output
mkdir -p build
export LEAN_PATH="$NT_LIB:$PWD/build:$(lean --print-libdir)"
lean -o build/LratBits.olean      LratBits.lean
lean -o build/LratBitsSound.olean LratBitsSound.lean
lean -o build/LratAdapter.olean   adapter-4.35/LratAdapter.lean   # adapter-4.31/ for Lean 4.31-4.34
lean -o build/BvdKC.olean         BvdKC.lean
lean -o build/BitsKernel.olean    BitsKernel.lean
lean AxCheck.lean
```

`AxCheck.lean` prints `[propext, Classical.choice, Quot.sound]` for the three soundness theorems
(checked on Lean 4.31.0 and 4.33.1, and with this recipe on 4.35.0).
