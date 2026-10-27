# In-house results

NativeTrust run on the author's published Lean results that use `native_decide`, set against the hand-built kernel
versions of the same theorems (Section "Our own native results" of the paper). Each project's summary lists the
toolchain, library version and run limits.

## Top-level files

- `inventory.tsv`: one line for each of the author's published results that has a Lean version. It records the
  Zenodo record, toolchain and published native facts, whether a hand-built kernel version exists, what it cost, and
  what was run here.
- `hand_tracks.tsv`: the hand-built kernel versions, one line per track (41 tracks of 31 results). Each line records the
  cost as stated in the record, with its source line, and the CPU-hours taken from it (`cpu_h`, with `about` marking
  estimates). The `coverage` column says what the track proves: the published result, a weaker bound or a part. The
  paper's total of about 1.03 million CPU-hours is the sum of `cpu_h` over the 23 results that also have a native
  version.
- `native_kernel_pairs.tsv`: the results whose records give the cost of the same computation both natively and in the
  kernel, with the ratio.
- `light_logs/`: the runs on the lighter results. `runs.log` records the start time and run time of each build and pass,
  `build*_<project>.log` are the native builds, `kfact_light3*.log` are the `kdecide` logs, `bohr_export_k5.log` is the
  Bohr K5 data export, and `guard.log` is the core-hour guard log. `light.theorems.tsv` lists, per theorem, the native
  facts and how many converted.
- `kfact_batch.log`, `kfact_batch2.log` to `kfact_batch7.log`, `kfact_batch9.log` and `kfact_batch10.log`: runner logs
  of the other `kdecide` runs, with the start time and exit code of each module.

## Project directories

| directory | result | run | converted |
|---|---|---|---:|
| `qec/` | the matching threshold of the rotated surface code under circuit noise, 16 theorems | driver on 109 of the 634 facts | 77 |
| `s13/` | the S(13) ≥ 45 sorting-network proof | 22 probe runs, and the static pass on one fact per class | 0 |
| `smale6v4/` | central configurations of six bodies | driver on 178 of the 546 facts in the modules that build | 56 |
| `ppt2/` | range-criterion counterexamples to the PPT² conjecture | driver on the 751 core facts and on 679 of the 1,039 row facts | 540 and 271 |
| `avw3sum/` | fine-grained lower bounds after the refutation of 3SUM and APSP | driver on the 11 facts | 11 |
| `poinc/` | the L¹ Poincaré constant of the Hamming cube | driver on the 3 facts | 2 |
| `zz/` | the Zhang–Zagier height bound | driver on the single fact | 0 |
| `tpupper/`, `tplower/` | totally positive Mahler measures, upper and lower bound | driver on 12 facts each | 3 and 0 |
| `maxterm2/` | maximum terms | driver on 12 facts | 0 |
| `char2/` | homological percolation in characteristic 2 | `kdecide` on 23 facts | 0 |
| `trace86/` | Schur–Siegel–Smyth traces | `kdecide` on 2 facts | 0 |
| `bohr/` | Bohr radii | `kdecide` on 1 fact | 0 |
| `romanoff/` | Romanoff's constant | `kdecide` on the 11 facts | 0 |
| `beatavg/` | the beat-the-average game | `kdecide` on 1 fact | 0 |
| `mm4/` | depth-9 local optimality of 4×4 matrix multiplication schemes | `kdecide` on 5 facts | 0 |
| `thrackle/` | thrackles | `kdecide` on 3 facts | 0 |
| `steiner/` | the Steiner ratio | `kdecide` on 10 facts | 0 |
| `pp12/` | projective planes of order 12 | `kdecide` on 4 facts | 0 |
| `mm3/`, `saw/`, `bhh/`, `chvatal_sankoff/`, `areal/` | five results that were not run | - | - |

Every directory holds `summary.tsv`, with one key-value pair per line, and `summary.md`, which describes the runs and
the commands used. The keys cover the result and source record, toolchain and library version, native and converted
facts, NativeTrust CPU-hours and wall time, and native-build CPU-hours. The `hand_` keys give the hand-built kernel
version and its build CPU-hours, as stated in its record. In `qec/` and `s13/`, the `method_` keys say how each number
was obtained. In the other directories, the `checks` key lists the runs and their limits. The summaries of the five
results that were not run give the reason.

## Driver runs

In `ppt2/`, `smale6v4/`, `avw3sum/`, `poinc/`, `zz/`, `tpupper/`, `tplower/` and `maxterm2/`:

- `<run>.ax.tsv` has the per-fact results, in the same columns as the study's (`../m2/ax/`). `<run>.heavy.ax.tsv`, where
  present, has the re-runs at 3,600 s and 96 GiB. In `smale6v4/` the re-runs follow the first-pass lines in the same
  file.
- `logs/<run>/` has the driver logs and the log of each fact that did not convert (`ax2_<module>_<n>.log`). Logs for
  converted facts and module listings are not included. The result tables have a line for every fact.
- `ppt2_theorems.tsv` and `smale6_theorems.tsv` have one line per native theorem: native facts, converted facts and
  status. `ppt2_counts.txt` counts the facts and theorems that were run, converted and cited, and lists the rows in the
  PPT² paper's Table A.1 whose cited theorems all converted. `selection_rows_a_cited.ax.tsv` lists the row facts in the
  cited theorems' closures, which were run first.
- `smale6v4/study_nt14_*.ax.tsv` are the study's results for the same packages, identical to
  `../sample/s_tejasvi_smale6_six_bodies_generic_v4_lean_*.ax.tsv`.

## `kdecide` runs

In `romanoff/`, `beatavg/`, `mm4/`, `thrackle/`, `steiner/`, `pp12/`, `char2/`, `trace86/` and `bohr/`:

- `ntk/` has copies of the fact modules in which `native_decide` is replaced by `kdecide` with compiled code switched
  off.
- `kfact.jsonl` has one line per module run, with these fields: facts, import build (`deps_rc`, `deps_s`), exit code,
  verdict (PROVED, TIMEOUT, MEMORY or FAILED), wall and CPU time, peak memory (`maxrss_gb`) in GiB (KiB / 2^20, despite
  the field name), time limit and error. Later lines add the tactic configuration, Lean options and command (`config`,
  `options`, `runner`). Lines without `options` are earlier attempts, and `summary.md` says which runs count.
- `logs/<module>_NTK.log` is the log of a run. The suffixes `.r2` and `.r3` mark re-runs.

## `qec/` and `s13/`

In `qec/`, `results/` holds the four driver runs (`qec_p1`, `qec_heavy`, `qec_unc` and `qec_sh1`), `checks/` the
corresponding fact files and `logs/` the logs. `build/` holds the native-build records, `blockers/` the static-blocker
searches, `supplement/` the Theorem 1.1 kernel supplement and its checks, and `analysis/` the per-theorem and per-family
tables. `thm11_same_box/` holds builds of the native and the hand-built kernel versions of Theorem 1.1, made on the
machine that ran the conversion. The directory has a separate README. Theorem 1.1 converts fully (61 of 61 facts).

In `s13/`, the driver did not run on all 1,724 facts. `s13_probe.ax.tsv` has one line per probe run, with the run
settings in added columns. `s13_facts.tsv` has one line per native fact: class, blocking constants of the class, and
runs. `s13_triage.tsv` holds the blocking constants found for each class representative. `data_chunks.tsv` lists the
length in characters of each data chunk, with its source line, and `release_s45_unconditional_axioms.txt` records the
axioms of `Sortnet.S13_ge_45`, the release's final theorem. The run records and core-hour guard logs are in
`logs/orchestration/`.
