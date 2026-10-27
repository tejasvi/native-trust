# Steiner ratio 43a v2

NativeTrust v15 converted none of the 10 native facts it checked.

The 482 shard facts and the skeleton facts read the data of the Zenodo record (data_C1..C4.tar.xz), which is not on
the study machine. The checks used kdecide on the statement (900 s, MemoryMax 100G), in a re-run of 2026-10-26
14:55-15:12Z from a fresh copy. The first run, at 05:37-05:55Z, gave the same verdicts. The earlier attempt on
S43Data.C1.Shard00000, whose data file is missing, is not included.

- `S43/Sample.lean`, added to the study copy only, holds the 6 facts of `S43Final.lean` and of the four
  `S43Data/Ck/Case.lean` modules that need no data file (`sizes_st`, `sizes_reg` and four monotonicity checks), with
  the statements unchanged. Its check ran out of memory after 304 s.
- In the release pilot case P80 (the same checker on 80 records), `Case.lean` (3 facts) ran out of memory after
  306 s. `Shard00000.lean` is blocked: `Float.scaleB` and `Float.round` (in `S43.evalVertex`) and `String.toNat?` (in
  `parseNats`) have no kernel definition, so the kernel cannot reduce the shard checks at any size.

No hand-built kernel track was published. The independent C checker of the records takes about 200 core-hours
(README.md:76).

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
