# String literals in the kernel: confirming the cause (2026-10-24)

**Question.** Is the quadratic kernel cost of string literals caused by `List.toByteArray`? Its
definition (core v4.34.0-rc2, `Init/Prelude.lean:3466`) is a loop of `r.push b` from
`ByteArray.empty`, and `Array.push` is `List.concat`.

**Test.**
- The literal is Repro.lean's: `"0 1 2 3 …"`, aperiodic, cut to N characters.
- The theorem is `d.utf8ByteSize > 0`, checked by `decide +kernel`, on Lean v4.34.0-rc2 with one
  thread.
- **A (original):** the kernel unfolds the literal to `String.ofList [chars]`, whose bytes are
  `List.utf8Encode` = `(flatMap utf8EncodeChar).toByteArray`.
- **B (one-step):** `d` is first bridged to `NativeTrust.ofListFast [chars]`.
  - `ofListFast` is `String.ofList` with `List.toByteArray` replaced by `⟨bytes.toArray⟩`, which
    builds the array in one step.
  - It is proved equal to `String.ofList` by `ofList_eq_ofListFast` (from
    `NativeTrust/StrFast.lean`). The bridge `d_eq : d = d2` is that theorem applied to the literal's characters.
  - The goal is then `rw [d_eq]; decide +kernel`.
  - The proof of `t` depends only on [propext, Quot.sound].
- **Z:** the baseline of the B files: `import Lean`, the literal and the bridge, with no
  `decide +kernel`.
- Files: `gen.py` and `run.sh`; the measured outputs are summarized in the tables above.
- Memory is max RSS in KiB; MiB = KiB / 1024 and GiB = KiB / 1048576.

**Results.** Columns are the raw `/usr/bin/time` values, and the kernel cost above the Z baseline:

| N chars | Z: wall s / RSS KiB | B: wall s / RSS KiB | B − Z | A: wall s / RSS KiB | A − Z |
|---:|---|---|---|---|---|
| 500 | 0.54 / 1,572,456 | 0.60 / 1,596,156 | 0.06 s / 23 MiB | 4.42 / 2,616,412 | 3.88 s / 1.00 GiB |
| 1,000 | 0.58 / 1,575,996 | 0.66 / 1,612,720 | 0.08 s / 36 MiB | 17.29 / 5,745,464 | 16.71 s / 3.98 GiB |
| 2,000 | 0.57 / 1,579,100 | 0.80 / 1,647,220 | 0.23 s / 67 MiB | 70.44 / 18,230,728 | 69.87 s / 15.88 GiB |
| 4,000 | 0.58 / 1,582,224 | 1.02 / 1,716,540 | 0.44 s / 131 MiB | (not run) | |
| 8,000 | 0.56 / 1,591,412 | 1.58 / 1,854,344 | 1.02 s / 257 MiB | (not run) | |

**Reading.**
- The original path grows 4× per doubling in both time and memory, i.e. quadratically.
- With only `List.toByteArray` replaced, memory grows 2× per doubling (23 → 36 → 67 → 131 →
  257 MiB), i.e. linearly, at about 32 KiB per character. Time also grows about 2× per doubling
  once it is measurable.
- At 2,000 characters the one-step path uses 67 MiB instead of 15.9 GiB and 0.23 s instead of 70 s.
- At 8,000 characters it takes 1.0 s and 257 MiB. By the earlier fit, the original path would need
  roughly 250 GiB there.
- **The cause is confirmed:** the `Array.push` fold in `List.toByteArray`.
