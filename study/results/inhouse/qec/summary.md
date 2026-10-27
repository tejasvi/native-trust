# QEC threshold: NativeTrust v15 on the native-only Lean formalization (run of 2026-10-26)

Every `native_decide` fact in the native formalization of the QEC threshold theorems was run with the study driver at
the study limits. Theorem 1.1, the only theorem whose facts all converted, received a kernel supplement, checked as in
the paper's independent checks. Two runs without the time limits measured the cost of the facts that did not convert.

## Inputs

- Project: v2 supplement, Zenodo 10.5281/zenodo.23485205. lean4/ is the git export of commit 643d947 (frozen v2 head
  c19066d + a README edit), without its committed logs/. Toolchain leanprover/lean4:v4.35.0-rc3, Mathlib c55e6e786f49
  (v4.35.0-rc3). The box cannot reach github.com, so `lake exe cache get` failed (build/cache_get.out). Instead, the
  prebuilt package set at the manifest revisions (Mathlib and 8 others) was copied in and checked file by file (sha256
  of all 146,639 files identical). `lake build --no-build Mathlib` then found nothing to build.
- Library: NativeTrust v15, manifest 6b378a8e59a328a9e9816b38d36f519ba46791204586556fe20b752deb16b3b6, box build /home/ntbuild/nt_fix14/v4.35.0-rc3, built with the same script as the other 14 toolchains.

## Native build

`lake build QEC QECComp` builds the library but not the check modules that hold the native facts. The project builds
those with its own scripts, which load the compiled core with `--load-dynlib` (lake would interpret them, about 40
times slower). The scripts ran in `verify_all.sh` order with `JOBS=32`, without `run_checks.sh`. That script builds the
390 modules for the kernel-only Theorem 1.1, a version with no native facts. Without them, the two kernel-only modules
in `run_final.sh` fail at import. The native build took 17.19 CPU-h: 17.12 in the check scripts (55.8 min wall, 606
modules) and 275 CPU-s for the library. build/checks.log has the times per script, build/project_logs/ the times per
module.

## Driver and runs

The driver is a copy of the study driver `m2_axioms5.py` (scripts/m2_axioms5_cg2.py) with three changes. The
per-process memory cap is a cgroup `memory.max` in a subtree that systemd delegates (scripts/drv_launch_v2.sh) instead of
`ulimit -v`, tested by scripts/cgtest_v2.py. Phase-2 facts are compiled with `-o`, so a supplement can import their
proofs. Listings are reused across runs. The runs used the default configuration (`split := 8`) and `--skip-build`.
The project has 634 facts in 593 modules, none inside definitions. results/ holds the per-run results, logs/ the
per-fact logs and checks/ the check files. The runs:

- pass 1, 900 s / 48 GiB, up to 32 processes (`qec_p1`): a pilot of 13 facts (one per check family), the 84 other light
  facts, and a stratified sample of 12 of the 541 heads/headsS/cover facts (one per family and model);
- heavy pass, 3,600 s / 96 GiB, 4 processes (`qec_heavy`): the 16 light-fact resource failures, plus headsS8_0;
- without the time limits, 96 GiB: heads8_0 and cover8_0_3, one process each, up to 4 h (`qec_unc`), and heads8_0 with
  the library shard option, shard 1 of 342 (head 0 alone), 3,600 s (`qec_sh1`).

Of the 541 heads/headsS/cover/heads8_size facts, 525 were not run. All 16 sampled ones timed out at 900 s, and
headsS8_0 also at 3,600 s. Running the rest would cost about 135 CPU-h in pass 1 alone, so they are reported as
resource failures at the study limits, judged from the sample.

## Results

Of the 634 facts, 77 converted, 32 ran out of time or memory, and 525 count as resource failures from the sample. None
failed on a blocker, and none fell into the other or not-run classes. 17 facts were re-run in the heavy pass. The fact
runs took 9.36 CPU-h (pass 1 6.89 h, heavy pass 2.47 h), plus 4.13 h for the runs without the time limits. 16 theorems
have native facts, and 400 facts have static blockers.

The per-theorem table is analysis/theorems.tsv. In it, `resource` marks facts that were run and ran out of time or
memory. `resource_sampled` marks facts of a sampled family that were not run (see above).

| theorem | native facts | converted | resource | resource (sampled) | CPU-h of its facts | not converted |
|---|---|---|---|---|---|---|
| `QEC.Circ.thm11_circuit_native` | 61 | 61 | 0 | 0 | 1.68 |  |
| `QEC.Circ.thm12_circuit_native` | 131 | 61 | 4 | 66 | 2.57 | cover8(28), heads8(40), heads8_size(1), tabCheck_native(1) |
| `QEC.Circ.thm12b_circuit_native` | 132 | 62 | 4 | 66 | 3.66 | cover8(28), heads8_size(1), headsS8(40), tabCheckP8(1) |
| `QEC.Circ.thm13a_lean_native` | 63 | 62 | 1 | 0 | 1.81 | tabCheckL(1) |
| `QEC.Circ.thm13b_lean_native` | 132 | 62 | 4 | 66 | 2.63 | coverL(28), heads8_size(1), headsL(40), tabCheckL(1) |
| `QEC.Circ.thm13b_native` | 132 | 62 | 4 | 66 | 2.63 | coverL(28), heads8_size(1), headsL(40), tabCheckL(1) |
| `QEC.Circ.thm13c_lean_native` | 132 | 62 | 4 | 66 | 2.63 | coverL(28), heads8_size(1), headsSL(40), tabCheckPL(1) |
| `QEC.Circ.thm13c_native` | 132 | 62 | 4 | 66 | 2.63 | coverL(28), heads8_size(1), headsSL(40), tabCheckPL(1) |
| `QEC.Circ.thm81a_h2_native` | 63 | 62 | 1 | 0 | 1.81 | tabCheckH2(1) |
| `QEC.Circ.thm81a_helios_native` | 63 | 62 | 1 | 0 | 1.80 | tabCheckHl(1) |
| `QEC.Circ.thm81b_h2_native` | 132 | 61 | 5 | 66 | 2.70 | coverH2(28), heads8_size(1), headsH2(40), tabCheckH2(1), wOKH2(1) |
| `QEC.Circ.thm81b_helios_native` | 132 | 61 | 5 | 66 | 2.70 | coverHl(28), heads8_size(1), headsHl(40), tabCheckHl(1), wOKHl(1) |
| `QEC.Circ.thm81b_heron_native` | 132 | 61 | 5 | 66 | 2.71 | coverHe(28), heads8_size(1), headsHe(40), tabCheckHe(1), wOKHe(1) |
| `QEC.Circ.thm81c_h2_native` | 132 | 61 | 5 | 66 | 2.70 | coverH2(28), heads8_size(1), headsSH2(40), tabCheckPH2(1), wOKSH2(1) |
| `QEC.Circ.thm81c_helios_native` | 132 | 61 | 5 | 66 | 2.71 | coverHl(28), heads8_size(1), headsSHl(40), tabCheckPHl(1), wOKSHl(1) |
| `QEC.Circ.thm81c_heron_native` | 132 | 61 | 5 | 66 | 3.00 | coverHe(28), heads8_size(1), headsSHe(40), tabCheckPHe(1), wOKSHe(1) |

The per-family table is analysis/families.tsv. Its static blockers are constants without a kernel definition that
`#kernel_blockers` finds reachable (blockers/):

| family | facts | converted | resource | resource (sampled) | heavy re-runs | CPU-h | static blockers |
|---|---|---|---|---|---|---|---|
| QEC.checkAll_native | 1 | 1 | 0 | 0 | 0 | 0.000 |  |
| cover8 | 28 | 0 | 1 | 27 | 0 | 0.250 |  |
| coverH2 | 28 | 0 | 1 | 27 | 0 | 0.250 |  |
| coverHe | 28 | 0 | 1 | 27 | 0 | 0.250 |  |
| coverHl | 28 | 0 | 1 | 27 | 0 | 0.250 |  |
| coverL | 28 | 0 | 1 | 27 | 0 | 0.250 |  |
| critOKH2_native | 1 | 1 | 0 | 0 | 0 | 0.001 |  |
| critOKHl_native | 1 | 1 | 0 | 0 | 0 | 0.001 |  |
| critOKL_native | 1 | 1 | 0 | 0 | 0 | 0.001 |  |
| heads8 | 40 | 0 | 1 | 39 | 0 | 0.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| heads8_size | 1 | 0 | 1 | 0 | 0 | 0.250 |  |
| headsH2 | 40 | 0 | 1 | 39 | 0 | 0.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| headsHe | 40 | 0 | 1 | 39 | 0 | 0.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| headsHl | 40 | 0 | 1 | 39 | 0 | 0.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| headsL | 40 | 0 | 1 | 39 | 0 | 0.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| headsS8 | 40 | 0 | 1 | 39 | 1 | 1.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| headsSH2 | 40 | 0 | 1 | 39 | 0 | 0.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| headsSHe | 40 | 0 | 1 | 39 | 0 | 0.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| headsSHl | 40 | 0 | 1 | 39 | 0 | 0.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| headsSL | 40 | 0 | 1 | 39 | 0 | 0.250 | Float.log(40), System.Platform.getNumBits(40), mixHash(40) |
| nfl_X | 5 | 5 | 0 | 0 | 0 | 0.350 |  |
| nfl_Z | 5 | 5 | 0 | 0 | 0 | 0.346 |  |
| nmaxOKH2 | 1 | 1 | 0 | 0 | 0 | 0.000 |  |
| nmaxOKHe | 1 | 1 | 0 | 0 | 0 | 0.000 |  |
| nmaxOKHl | 1 | 1 | 0 | 0 | 0 | 0.000 |  |
| nmaxOKL | 1 | 1 | 0 | 0 | 0 | 0.000 |  |
| nmaxOKS8 | 1 | 1 | 0 | 0 | 0 | 0.001 |  |
| nmaxOKSH2 | 1 | 1 | 0 | 0 | 0 | 0.000 |  |
| nmaxOKSHe | 1 | 1 | 0 | 0 | 0 | 0.001 |  |
| nmaxOKSHl | 1 | 1 | 0 | 0 | 0 | 0.001 |  |
| nmaxOKSL | 1 | 1 | 0 | 0 | 0 | 0.001 |  |
| nty_X | 25 | 25 | 0 | 0 | 0 | 0.493 |  |
| nty_Z | 25 | 25 | 0 | 0 | 0 | 0.495 |  |
| tabCheckH2 | 1 | 0 | 1 | 0 | 1 | 0.122 |  |
| tabCheckHe | 1 | 0 | 1 | 0 | 1 | 0.121 |  |
| tabCheckHl | 1 | 0 | 1 | 0 | 1 | 0.121 |  |
| tabCheckL | 1 | 0 | 1 | 0 | 1 | 0.121 |  |
| tabCheckP8 | 1 | 0 | 1 | 0 | 1 | 0.121 |  |
| tabCheckPH2 | 1 | 0 | 1 | 0 | 1 | 0.122 |  |
| tabCheckPHe | 1 | 0 | 1 | 0 | 1 | 0.120 |  |
| tabCheckPHl | 1 | 0 | 1 | 0 | 1 | 0.121 |  |
| tabCheckPL | 1 | 0 | 1 | 0 | 1 | 0.121 |  |
| tabCheck_native | 1 | 0 | 1 | 0 | 1 | 0.122 |  |
| wOK8 | 1 | 1 | 0 | 0 | 0 | 0.017 |  |
| wOKH2 | 1 | 0 | 1 | 0 | 1 | 0.147 |  |
| wOKHe | 1 | 0 | 1 | 0 | 1 | 0.152 |  |
| wOKHl | 1 | 0 | 1 | 0 | 1 | 0.149 |  |
| wOKL | 1 | 1 | 0 | 0 | 0 | 0.071 |  |
| wOKS8 | 1 | 1 | 0 | 0 | 0 | 0.102 |  |
| wOKSH2 | 1 | 0 | 1 | 0 | 1 | 0.148 |  |
| wOKSHe | 1 | 0 | 1 | 0 | 1 | 0.447 |  |
| wOKSHl | 1 | 0 | 1 | 0 | 1 | 0.150 |  |
| wOKSL | 1 | 1 | 0 | 0 | 0 | 0.077 |  |

- No fact failed on a blocker at run time. The 400 heads/headsS facts have three reachable blockers: `mixHash` (the
  hash of `List` keys), `Float.log` (`QECComp.testF` in the search `searchM`) and `System.Platform.getNumBits` (the
  `USize` arithmetic in `HashMap`, which v15 handles by the word-size case split). Their evaluation is bounded, and none
  finished in time. The coverage, table, factor-bound and representative checks have no blocker.
- All 16 light resource failures ran out of memory. The ten type-table checks (`tabCheck…`, `tabCheckP…`) reach 48 GiB in
  about 150 s and 96 GiB in about 290 s. The He, Hl and H2 factor bounds (`wOK…`, `wOKS…`) reach 96 GiB in 330-710 s.
  The driver labels five of them `deep_recursion` because of a non-fatal copy note, but their processes were
  OOM-killed (`cg_oom_kill=1`). So Theorems 1.3(a) and 8.1(a) each miss one fact, the type table.

## Cost without the limits, compared with the hand-built kernel track

- heads8_0 covers heads 0..341 of the 8-step certificate in 8 pieces of 43. No piece finished in 4 h (14,399 CPU-s,
  10.2 GB), and head 0 alone (shard 1 of 342) did not finish in 3,600 s (9.3 GB). The hand-built track checks heads
  0..211 in 527 s (module QECKernel/c8/H0) and heads 0..388 in 527 + 575 + 571 = 1,673 s (modules H0-H2), or 4.3 s
  per head. Over all 13,658 heads of the 8-step certificate it takes 14.3 s per head (333 modules, 195,099 s). The
  sources are lean4_build/k3_build.txt in the v3 supplement (lines 1473, 937, 1581 for H0-H2) and the head ranges in
  lean4/QECKernel/c8/H*.lean (line 9). So one head costs NativeTrust more than 1,400 times as much as the hand-built
  check of heads 0..211. At that ratio the 400 heads facts (136,580 heads, 551.8 hand-built module-hours) would need
  more than 7.7e5 CPU-h, and at least 1.35e5 CPU-h even at 3,567 s per head.
- cover8_0_3 is the smallest coverage fact. Piece 1 of 8 took 0.64 s, and piece 2 ran out of 96 GiB after 470 s. In
  pass 1 it timed out at 900 s at 8.1 GiB. The hand-built module QECKernel/Cov/C0_3_0 checks the same basis and
  distance for all five models in 13 s (lean4_build/k3_build.txt line 4149). All hand-built coverage (107 files) took
  40.52 module-hours (lean4_build/costs.txt line 18).

## Kernel supplement of Theorem 1.1 and its checks (supplement/)

`Supp_thm11.lean` imports NativeTrust, the 61 fact modules the driver wrote (supplement/fm_thm11.txt) and
`QEC.ChecksN.Thm11V2`, and runs `kernelize QEC.Circ.thm11_circuit_native` (3.1 s). `….kernel` depends only on propext,
Classical.choice and Quot.sound, and it has the same type as the original (Expr ==). A fresh process running the
study's statement-check script printed `STMT same=1 defeq=0 diff=0 missing=0 nonstd_axioms=0 control_originals_nonstd=1`.
leanexport wrote 2,214,868 lines. The first attempt failed because the elan proxy has no default toolchain
(supplement/Supp_thm11.export.err). The second ran with the toolchain first on PATH. nanoda, which allows only the
standard axioms and treats any other axiom as a hard error, printed `Checked 21775 declarations with no typechecker errors, 1 pretty printer
errors: [ "Unable to print axioms", ]` (5228.41 s wall, 5180.21 s user, 8961380 KB).

## Commands (box, as ntbuild in systemd units with MemoryMax)

- native build: `scripts/setup_v2.sh`, then `scripts/run_checks_all_v1.sh` (unit MemoryMax=256G);
- driver: `systemd-run -p Delegate=yes -p MemoryMax=600G --uid=ntbuild drv_launch_v2.sh m2_axioms5_cg2.py qec
  <project> --skip-build --nt-root /home/ntbuild/nt_fix14 --jobs 32 --fact-timeout 900 --fact-mem 48
  --results-suffix _p1 --reuse-listing [--include-file pilot_re.txt | --exclude "^(heads|cover)" | --include-file
  strat_re.txt]`; heavy pass `--jobs 4 --fact-timeout 3600 --fact-mem 96 --results-suffix _heavy --include-file
  heavy_re.txt`; without the limits `--jobs 2 --fact-timeout 14400 --fact-mem 96 --results-suffix _unc --include-file
  unc_re.txt`; shard `--fact-timeout 3600 --fact-mem 96 --results-suffix _sh1 --include-file h80_re.txt
  --extra-config "shards := 342, shardOnly := 1"`;
- static blockers: `scripts/blockers_v1.sh`; tables: `scripts/analyze_v2.py`; supplement: `scripts/fm_for_v1.py`,
  `scripts/supp_build_v1.sh`, `scripts/supp_export_v1.sh`.
