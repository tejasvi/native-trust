# smale6 six bodies v4, native version

NativeTrust v15 converted 56 native facts (54 in sections6-9, 2 in sections3-5) of the 546 in the modules that
`lake build` builds in this copy, the same facts as the previous version (v14). At theorem level, 18 theorems are
fully converted, 15 in sections6-9 and 3 in sections3-5 (smale6_theorems.tsv), and none of them is a headline theorem.

The native headline of version 2, `CC6Compose.main_theorem`, depends on 3,158 `native_decide` axioms: 2,714 from
lean6 (1,928 core cofactor certificates, 660 F2S, 125 F34S, 1 F1), 443 from lean6_special and 1 from the composition
(lean/full/README.md:99-103, 29-32). The version 3 headline `main_theorem_v3` depends on 2, `Count.kc_f4_ok` and
`Count.s12_f4_ok` (logs/release_check_v3/check_v3.log:4257-4261), and v15 converts neither. kc_f4_ok times out at
900 s and at 3,600 s, and s12_f4_ok is blocked. The version 4 headline `main_theorem_v4` depends on none. The facts of
the earlier native checks that the default build does not build (about 1,326 in this copy) were not checked.

The per-fact driver ran on the copy of the release from the earlier study, stratified by the study verdicts: all 126
non-memory facts of sections6-9, 40 of its 408 memory failures (seed 20261026) and all 12 facts of sections3-5, at
900 s and 48 GiB. The heavy pass then ran at 3,600 s and 96 GiB on 37 resource failures (26 D88.Boxes, 6 D88.Trop, 4
in sections3-5 and 1 timeout). Compared with the study, the 54 PROVED facts stayed PROVED and the 40 sampled memory
failures still ran out of memory. Of the 71 blocked facts, 59 stay blocked and 12 now run out of memory, because the
blocking constant is gone. The heavy pass converted none: 36 ran out of memory at about 92 GiB and 1 timed out.
Extrapolated to all 534 facts of sections6-9, the counts are PROVED 54, blocked 59, memory 420 and timeout 1, and pass
1 on all of them would take about 29 h of process time.

The release axiom logs list 1,097 native axioms in sections3-5 (F1 8, F2 429, F2S 660). The study copy built only 12
of them, because scripts, not `lake build`, build the F2/F2S chunk modules. The sections3-5 numbers therefore cover
about 1% of its native facts.

At theorem level (the release `#print axioms` logs: sections6-9/logs/integration/axioms_all.log, and logs/f1, f2 and
f2s of sections3-5), 75 theorems in sections6-9 have native axioms: 15 converted, 19 did not convert (a native axiom
that v15 checked failed) and 41 are unchecked (axioms not resampled). In sections3-5, 22 theorems have native axioms:
3 converted, 14 did not, 5 unchecked. The
converted theorems are Lean6.Special.D88.Trop.{kc,n4}_{G_mem,size,units}, Lean6.Special.D98.{P93_eval_1_2_7_ne_zero,
check_1_2_7, check_1_2_7_min, check_1_2_8, check_rho_product, lemma69_check_1_2_7, lemma69_check_1_2_8,
lemma69_check_2_3_11, no_common_root_1_2_7} and L6F1.{F1_n4, check_n4, n4json_sha256}. The v4 kernel track already
checks the published theorems in the kernel.

The hand-built kernel track took 1,178.3 CPU-hours: 963 for the lean6 (sections3-5) stages in the v3 release run
(lean/full/README.md:335-336), 45.0 for the lean6_special kernel stages with the libraries (:342-343) and 170.3 for
the sections6-9 stage dim in the v4 release run (:284).

## Method

The library is NativeTrust v15, the build `nt_fix14` for the toolchain `leanprover/lean4:v4.35.0-rc3`
(`/home/ntbuild/nt_fix14/v4.35.0-rc3`). The sha256 over its `NativeTrust/*.lean` and `NativeTrust.lean` files, sorted by
path, is `77a403a5372f566c…`. All runs were on the study machine as the user `ntbuild`, each run in a systemd unit with a
memory cap (MemoryMax). Projects were copied read-only into fresh directories. They use the shared rc3 Mathlib copy
(Mathlib `c55e6e786f49`, as pinned by every project here).

A native fact is checked in one of two ways.

- **Per-fact driver** (`m2_axioms5.py`), on a package whose native build exists. For each native axiom
  (`…._native.native_decide.ax_…`) a check module imports the fact module and runs
  `prove_native_axiom_nth MODULE i (config := { split := 8, trace := true })`, with `set_option Elab.async false`,
  `maxHeartbeats 0` and `maxRecDepth 1000000`, under a per-fact time limit and memory limit. Pass 1 uses the study
  limits (900 s, 48 GiB), and a heavy pass (3,600 s, 96 GiB) then runs on all or a sample of the resource failures.
  Results are in `<run>.ax.tsv`, one row per check. The driver appends rows, so the first row of a fact is its pass-1
  result and the last row its heavy-pass result, if the heavy pass ran on it. Per-fact logs are in `logs/`.
- **kdecide on the statement** (`ih_kfact_v5.py`), where the native build is too costly or its data are not
  available. A copy of the fact module (`<module>_NTK.lean`) has every `native_decide` tactic replaced by
  `kdecide (config := { native := false, split := 8, maxRecDepth := 1000000 })` and the three driver options after
  the imports. The copy is built with `lake build` under `timeout -k 30 <limit>` (900 s unless stated), in a unit with
  MemoryMax 100G. No compiled code is used. Results are in `kfact.jsonl`, one line per fact module, and the logs are in
  `logs/`.

A fact counts as **converted** when its check ends PROVED: the kernel checked a proof of the native-axiom statement
(driver) or of the theorem itself (kdecide), and no native axiom remains.

### `<run>.ax.tsv` columns

`package`, `module`, `axiom`, `tactic`, `inner`, `verdict`, `reason`, `kernel_ms`, `maxrss_kb`, `secs`, `blockers`,
`notes`. The verdicts:

- `PROVED`;
- `FAILED` with reason `blocked`: a constant without a kernel definition is reachable, and `blockers` names it;
- `ERROR` with reason `memory`: the check went over its memory limit;
- `TIMEOUT` (`900s` or `3600s`);
- `NOT_BUILT` rows (axiom `-`) are modules without a native build, not facts.

`secs` is the wall time of the per-fact check process, `maxrss_kb` its peak resident memory, and `kernel_ms` the kernel
time that NativeTrust reports.

### `kfact.jsonl` fields

- `module`: the fact module (dotted name);
- `facts`: number of `native_decide` tactics replaced;
- `deps_rc`, `deps_s`: exit code and seconds of the first step, which builds the module imports;
- `rc`: exit code of `lake build` of the kdecide copy under `timeout -k 30 timeout_s`;
- `verdict`: `PROVED` (rc 0, every fact kernel-checked), `TIMEOUT` (rc 124), `MEMORY` (rc 137, out of memory, or
  lean killed by signal 9 under the unit MemoryMax), `FAILED` (any other error, see `error`), `NOFACT` (no
  `native_decide` tactic found, so nothing was built);
- `wall_s`: wall seconds of that build;
- `cpu_s`: user + system seconds from `/usr/bin/time`, an undercount when the time limit kills the build;
- `maxrss_gb`: peak resident memory of the largest process, in GiB (KiB / 2^20), despite the field name;
- `timeout_s`: the time limit;
- `error`: the first `error:` line of the build log (at most 300 characters);
- `config`: the kdecide configuration;
- `options`: the options set after the imports;
- `log`: the log file under `logs/`;
- `note`: a changed environment, if any;
- `runner`: the command that checked the copy, when it was not `lake build` (`lake env lean FILE`, used for a larger
  thread stack or where `lake build` would build a whole precompiled library).

Lines without `options` come from earlier versions of the runner script, and the later lines for the same module
supersede them. Those versions replaced only `by native_decide`, which left native any `native_decide` tactic that
stood on its own line, and they did not set the driver options.
