# String literals in the Lean kernel: cost (NativeTrust / BerryEsseen cover data)

Measured 2026-10-23, 21:46 to 22:06 UTC, on the shared box (96 cores, load about 47).
Every run is one `lean` process with `ulimit -v` 24 GB, `timeout 300`, `-j1 --tstack=1048576`, `ulimit -s unlimited`,
`LEAN_NUM_THREADS=1`, at most 4 at once. Unless a row says otherwise, each test file has
`set_option maxHeartbeats 0` and `set_option maxRecDepth 1000000`. Time is wall time (`%e`).
Peak is max RSS (`%M`) in GB (KB / 10^6). Toolchain is v4.34.0-rc2 unless the row says v4.35.0.
Most rows are single runs. Repeated runs differed by up to about 8 % (`613/200 ` x 8000: 51.6, 55.1, 47.4 s).
Raw data is in `results/*.tsv` (one file per batch) and `results/table_all.md` (all runs merged by `table.py`).

## 1. Minimal reproduction

The files import nothing beyond the prelude: no Mathlib, no BerryEsseen, no NativeTrust.

| file | content (1,000 chars) | v4.34.0-rc2 | v4.35.0 |
|---|---|---|---|
| `Repro.lean` | `"0 1 2 3 ..."` cut to 1,000 chars (aperiodic, digits and spaces only); `theorem t : d.utf8ByteSize > 0 := by decide +kernel` | 19.09 s, 4.66 GB | 18.92 s, 4.57 GB |
| `ReproControl.lean` | `"613/200 "` repeated (period 8, same character classes) | 0.81 s, 0.59 GB | 0.71 s, 0.58 GB |
| `ReproArray.lean` | no strings: `(bs.foldl Array.push #[]).size > 0` over the 1,000 UTF-8 bytes of Repro's literal | 20.62 s, 4.66 GB | 19.71 s, 4.57 GB |

`Repro.lean` also needs neither `maxRecDepth` nor a large stack at this size:
- without `maxRecDepth`: 19.20 s, 4.66 GB;
- with default lean flags and the default `ulimit -s`: 19.71 s with `maxRecDepth`, 21.02 s without it, 4.66 GB both times.

The 2,000-char version (`gen4.py ... cnt:2000:ubs:dk`) takes 79.16 s and 17.14 GB.
The package's own DW21 literal (7,824 chars), pasted into a file that imports nothing else (`full/`):

| setting | result |
|---|---|
| with `maxRecDepth 1000000` | `std::bad_alloc` at 61.67 s, 20.30 GB RSS (the 24 GB limit) |
| without `maxRecDepth` | `(kernel) deep recursion detected, use set_option maxRecDepth` after 1.27 s |

So both earlier package observations reproduce without the package:
- K1/P0: out of memory when `maxRecDepth` is raised;
- Q1: fast deep-recursion error when it is not.

## 2. Growth with literal size

All rows: `d.utf8ByteSize > 0`, `decide +kernel`. D = number of distinct non-empty substrings of the literal's UTF-8 bytes (`dsub.py`, suffix automaton).

| content | chars | D | v4.34.0-rc2 | v4.35.0 |
|---|---|---|---|---|
| DW21 prefix (aperiodic) | 250 | 30,557 | 1.61 s, 0.74 GB | 1.50 s, 0.73 GB |
| | 500 | 123,311 | 5.07 s, 1.52 GB | 5.02 s, 1.49 GB |
| | 1,000 | 494,506 | 21.19 s, 4.63 GB | 21.74 s, 4.54 GB |
| | 2,000 | 1,901,134 | 84.31 s, 16.37 GB | 81.24 s, 16.04 GB |
| | 4,000 | 7,740,835 | bad_alloc at 73.83 s, 20.34 GB (24 GB limit) | |
| | 7,824 (full) | 29,931,381 | bad_alloc at 61.67 s, 20.30 GB | |
| `'a'` repeated | 1,000 / 4,000 / 8,000 / 16,000 | = chars | 0.49 s, 0.53 GB / 1.48 s, 0.70 GB / 3.09 s, 0.92 GB / 5.44 s, 1.38 GB | 8,000: 2.66 s, 0.91 GB |
| `"613/200 "` repeated | 1,000 / 2,000 / 4,000 | 7,971 / 15,971 / 31,971 | 0.70 s, 0.59 GB / 1.24 s, 0.70 GB / 3.05 s, 0.93 GB | 1,000: 0.80 s; 4,000: 3.50 s |
| | 6,000 / 7,000 / 8,000 / 12,000 | 47,971 / 55,971 / 63,971 / 95,971 | 17.37 s, 1.17 GB / 27.06 s, 1.28 GB / 51.58 s, 1.40 GB / 264.65 s, 1.86 GB | 8,000: 45.19 s, 1.37 GB |

The growth rate depends on content:
- Aperiodic literals: time and memory both grow about 4x per doubling, i.e. quadratically.
- Constant literals: about linear.
- `"613/200 "`: memory is linear, but time grows faster (see section 7).

## 3. Repetition and character classes

All rows: `d.utf8ByteSize > 0`, `decide +kernel`, v4.34.0-rc2. `perP` = a random block of P characters, drawn from DW21's 14-character alphabet and repeated.

| content | chars | D | time, peak |
|---|---|---|---|
| per16 | 2,000 / 4,000 / 8,000 | 31,875 / 63,875 / 127,875 | 2.15 s, 0.83 GB / 4.21 s, 1.20 GB / 7.61 s, 1.93 GB |
| per64 | 1,000 / 2,000 | 61,924 / 125,924 | 4.10 s, 1.03 GB / 6.14 s, 1.62 GB |
| per256 | 1,000 / 2,000 | 222,992 / 478,992 | 10.79 s, 2.37 GB / 22.26 s, 4.55 GB (v4.35.0: 20.59 s, 4.46 GB) |
| per1024 | 2,000 | 1,522,184 | 69.98 s, 13.27 GB |
| per2 / per4 / per8 | 8,000 | 15,999 / 31,994 / 63,970 | 3.13 s, 0.99 GB / 4.06 s, 1.13 GB / 4.94 s, 1.39 GB |
| random over DW21 alphabet | 250 / 500 / 1,000 | 31,019 / 124,385 / 498,517 | 1.65 s, 0.74 GB / 5.04 s, 1.53 GB / 21.26 s, 4.66 GB |
| random digits | 1,000 | 498,178 | 20.57 s, 4.66 GB |
| random over {0,1} | 1,000 | 491,518 | 21.23 s, 4.61 GB |
| random punctuation | 1,000 | 499,049 | 19.27 s, 4.67 GB |
| all spaces / all `\n` | 1,000 | 1,000 | 0.46 s, 0.53 GB / 0.36 s, 0.53 GB |
| random 2-byte chars (αβγ…) | 250 (500 bytes) | 123,674 | 5.63 s, 1.52 GB |
| random 3-byte chars (∀∃…) | 250 (738 bytes) | 269,206 | 12.96 s, 2.74 GB |
| random 4-byte chars (emoji) | 250 (1,000 bytes) | 492,118 | 19.00 s, 4.62 GB (v4.35.0: 20.72 s, 4.52 GB) |

The character class does not matter. Digits, punctuation, spaces, newlines and a two-letter alphabet all cost the same at equal D. Non-ASCII characters cost the same as ASCII with the same number of bytes. Only repetition matters, i.e. how many distinct byte substrings the literal has.

**Memory model.** A least-squares fit over all 64 completed `utf8ByteSize` / `decide +kernel` runs gives:

    peak_KB - 472,744 = 48.6 KB * bytes + 8.27 KB * D

Its largest relative error is 2.1 % (`table.py`; 472,744 KB is a trivial run that only loads a 2,000-char literal).

| literal type | D |
|---|---|
| aperiodic | about bytes² / 2 |
| period p | about p * bytes |
| one repeated character | bytes |

Time roughly follows D too, at about 43 to 47 µs per distinct substring once D is much larger than the byte count (21.19 s at D = 0.49 M, 84.31 s at D = 1.90 M, 22.26 s for per256 at D = 0.48 M). The exception is the `"613/200 "` block (section 7).

Extrapolating the fit, which was not run: the full DW21 literal (D = 29.9 M) would need about 248 GB and about 21 min.

## 4. Operations and checking methods (500 chars, v4.34.0-rc2)

| statement (all `decide +kernel` unless noted) | DW21 prefix | `"613/200 "` x |
|---|---|---|
| `d.utf8ByteSize > 0` | 5.07 s, 1.52 GB | 0.47 s, 0.53 GB |
| `(d == d2) = true` (d2 = separate identical literal) | 5.88 s, 1.53 GB | 0.57 s, 0.54 GB |
| `d = d2` | 5.92 s, 1.53 GB | 0.44 s, 0.54 GB |
| `d = d` | 6.14 s, 1.53 GB | 0.58 s, 0.54 GB |
| `d.toList.length > 0` | 18.40 s, 4.65 GB | 14.99 s, 3.67 GB |
| `d.length > 0` | 21.54 s, 4.65 GB (v4.35.0: 18.73 s, 4.57 GB) | 16.43 s, 3.66 GB (v4.35.0: 13.54 s, 3.61 GB) |
| `d.length > 0`, 250 / 1,000 chars | 5.18 s, 1.53 GB / 73.42 s, 17.03 GB | |
| `d.toList.length > 0`, 250 chars | 5.46 s, 1.53 GB | |
| `theorem : d = d2 := rfl` (2,000 chars) | 0.15 s, 0.47 GB (v4.35.0: 0.18 s) | |
| `theorem : d = d := rfl` (2,000 chars) | 0.21 s, 0.47 GB | |

| method on `d.utf8ByteSize = 500` (DW21 prefix, 500 chars) | time, peak |
|---|---|
| `by decide +kernel` | 5.40 s, 1.52 GB |
| `by rfl` | 8.99 s, 1.52 GB |
| term-mode `rfl` | 16.77 s, 1.52 GB (v4.35.0: 15.86 s, 1.49 GB) |
| `(Nat.decEq lhs rhs).decide = true := by decide +kernel` | 5.90 s, 1.52 GB |

Findings:
- Every operation that looks at the string's content costs at least as much as building its byte array:
  - `utf8ByteSize`, `==` and `decide (=)` cost about the same.
  - `length` and `toList` cost about 3 to 4x more and are still quadratic (250 to 1,000 chars: 1.53 to 4.65 to 17.03 GB).
  - For `length` and `toList`, periodic content saves only about 20 %.
- A proof of literal equality by `rfl` costs nothing: there is no expansion.
- The checking method changes time, not peak memory. The `rfl` variants add elaboration time; the kernel's part is the same.

## 5. Isolating the cost (1,000 chars, v4.34.0-rc2; `l : List Char` and `bs : List UInt8` written as explicit list literals, no string literal)

| statement (`decide +kernel`) | random (DW21 alphabet) | `"613/200 "` x |
|---|---|---|
| string literal `d.utf8ByteSize > 0` | 21.26 s, 4.66 GB | 0.70 s, 0.59 GB |
| `(String.ofList l).utf8ByteSize > 0` | 22.52 s, 4.68 GB (v4.35.0: 22.27 s) | 1.08 s, 0.61 GB |
| `(l.flatMap String.utf8EncodeChar).length > 0` | 0.61 s, 0.53 GB (v4.35.0: 0.56 s) | |
| `(l.flatMap String.utf8EncodeChar).toByteArray.size > 0` | 22.92 s, 4.68 GB | 1.07 s, 0.61 GB |
| `bs.toByteArray.size > 0` | 24.03 s, 4.66 GB | |
| `bs.toArray.size > 0` (`List.toArray xs := .mk xs`, Prelude:3233) | 0.61 s, 0.51 GB | |
| `(bs.foldl Array.push #[]).size > 0` | 23.34 s, 4.66 GB (v4.35.0: 22.16 s) | 1.10 s, 0.59 GB |

Findings:
- The literal costs the same as `String.ofList` of its character list.
- UTF-8 encoding is cheap: `flatMap` costs 0.61 s.
- All of the cost, including the content dependence, is in turning the byte list into an array by repeated `Array.push`. Any left fold of `Array.push` has the same cost, with no string involved.

## 6. Mechanism

Line numbers are for v4.34.0-rc2 `src/lean`. v4.35.0 has the same definitions at the line given in brackets.

1. **Literal to `String.ofList`.** To take a string literal apart, it is rewritten as `String.ofList [Char.ofNat c1, ...]`:
   - The elaborator-side mirror is `Lean.Expr.toCtorIfLit` (`Lean/Meta/WHNF.lean:23-28`, identical in v4.35.0): `.lit (.strVal v) => whnf (mkApp (mkConst ``String.ofList) (toExpr v.toList))`.
   - `ToExpr Char` (`Lean/ToExpr.lean:189-190`) gives `Char.ofNat (lit n)`.
   - The kernel's C++ is not in the toolchain. That the kernel does the same is inferred from section 5, where the literal and `String.ofList l` cost the same.
2. **`String.ofList` builds the bytes with a push fold:**
   - `String.ofList data := ⟨List.utf8Encode data, .intro data rfl⟩` (`Init/Prelude.lean:3560-3561` [3701]); `String` is `ofByteArray :: toByteArray : ByteArray, isValidUTF8` (3540-3546).
   - `List.utf8Encode l := l.flatMap String.utf8EncodeChar |>.toByteArray` (3517-3518 [3658]).
   - `List.toByteArray bs := loop bs ByteArray.empty`, with `loop (b :: bs) r = loop bs (r.push b)` (3466-3470 [3607-3611]).
   - `ByteArray.push ⟨bs⟩ b = ⟨bs.push b⟩` (3459-3460 [3600-3601]).
   - `Array.push a v := ⟨List.concat a.toList v⟩` (3338-3339 [3479-3480]).
   - `List.concat` is structural recursion: `concat [] b = [b]`, `concat (a :: as) b = a :: concat as b` (3127-3129 [3268-3270]).
3. **Reading the size walks that chain:**
   - `String.utf8ByteSize s := s.toByteArray.size` (3640-3641 [3781-3782]).
   - `ByteArray.size ⟨bs⟩ = bs.size` (3479-3480).
   - `Array.size a := a.toList.length` (3269-3270).
   - The kernel reduces `List.length` of `concat (concat (... (concat [] b1) ...) b(n-1)) bn`. Each cons it exposes requires reducing a nested `concat` chain.
4. **Why content matters.** Memory fits 8.27 KB per distinct byte substring D, plus 48.6 KB per byte, to within 2.1 % (section 3).
   - This fits if each nested `concat` term, which encodes a byte run b_i..b_k, is reduced once per distinct run. Structurally equal runs would then share one reduction, presumably through the kernel's caches.
   - That gives about n²/2 terms for aperiodic data, about p·n for period p, and n for a constant string.
   - This interpretation is inferred from the fit; I did not check it against the C++ source.
5. **`length` / `toList` add a decode pass:**
   - `String.length b := b.toList.length` (`Init/Data/String/Length.lean:25-26`).
   - `String.toList s := (String.Internal.toArray s).toList` (`Init/Data/String/Basic.lean:241-242`).
   - `Internal.toArray b := b.toByteArray.utf8Decode?.get _` (`Basic.lean:222-223`).
   - `ByteArray.utf8Decode?` (`Basic.lean:74-86`) is well-founded recursion `go i acc` that calls `utf8DecodeChar? b i` and `acc.push c` until `i < b.size` fails.
   - I did not isolate the costs inside this pass.
6. **Equality:** `String.decEq` (`Prelude:3570-3575`) matches both arguments down to `⟨⟨⟨s⟩⟩, _⟩`, which forces both byte arrays.
7. **Default `maxRecDepth` (512), no option set, DW21 prefixes:**
   - 1,500 chars: no error (still evaluating at the 20 s timeout, 6.48 GB).
   - 1,750 / 2,000 / 2,500 / 3,000 / 3,500 / 4,000 / 5,000 / 6,000 / 7,824 chars: `(kernel) deep recursion detected` within 0.5 to 1.3 s.
   - `'a'` x 2,000, `'a'` x 8,000 and `"613/200 "` x 4,000 fail the same way, so this limit depends on length, not content.
   - Raising `maxRecDepth`, as the earlier K1/P0 runs did, turns this fast error into the quadratic run in sections 2-3.

## 7. Open questions

- The kernel's C++ source (literal expansion, cache keys) is not in the toolchain. Steps 1 and 4 of section 6 are therefore inferred, from the Meta mirror and from the measurements.
- The `"613/200 "` block, and its rotation `"200 613/"`, is slow in time only. At 8,000 chars it takes 47 to 55 s, against 4.3 to 5.3 s for every other 8-char block tried (`613/201 `, `613/2000`, `61302000`, `01234567`, `abcdefgh`, `aaaaaaab`, random). Time is superlinear: 17 / 27 / 52 / 265 s at 6 / 7 / 8 / 12 thousand chars. Memory matches the model exactly. The cause is unexplained.
- It is not explained why repetition barely helps `length` / `toList`.
- Not tested:
  - other checkers (nanoda, lean4lean);
  - NativeTrust's own pipeline (`kdecide`). Earlier measurements there (S4000 3.2 s versus R4000 out of memory) agree with this picture;
  - other BerryEsseen literals besides DW21.

## Scripts (in this directory)

- `push.sh`: copies a file to the box.
- `gen.py` → `gen2.py` → `gen3.py` → `gen4.py` (each adds content kinds; never edited while a batch ran): write the test files.
- `run.sh` / `run2.sh` (run2 adds `FLAGS` / `KEEPSTACK`): run lean with the limits.
- `batch*.sh`: generate a batch and run it.
- `chain5.sh` to `chain10.sh`: queued batches.
- `make_repro.py`: writes the three Repro files.
- `dsub.py`: computes D.
- `table.py`: merges the results and fits the memory model.
- `inspect_data.py`: character histogram of a package literal.

Batch to directory map:

| directory | contents |
|---|---|
| b1, m1 | growth and character classes |
| m2 | operations, methods, isolation |
| m3 | v4.35.0 |
| m4, m6 | repetition and the `613/200 ` blocks |
| m5 | 4,000 chars, cnt 2,000, `length` at 1,000 |
| repro | the Repro files |
| rd, rd2 | `maxRecDepth` and stack variants |
| full | 7,824 chars |
| thr, thr2 | deep-recursion threshold |
