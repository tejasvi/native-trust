# Romanoff 45a v10, native version

NativeTrust v15 converted none of the 11 native facts, so no theorem gets a kernel-checked version from it.

| module | facts | verdict | wall s | peak GiB |
|---|---|---|---|---|
| RCert.G.BCheck (lean_u3g) | 1 | MEMORY | 267 | 101.1 |
| RCert.Cert45Check (lean) | 2 | MEMORY | 612 | 101.0 |
| Romanoff.G.S2.Native (lean_u3g) | 1 | MEMORY | 439 | 101.1 |
| RCert.M3.NCheck (lean) | 3 | MEMORY | 852 | 101.1 |
| RCert.M3G.NCheck (lean_u3g) | 4 | MEMORY | 848 | 101.1 |

All five modules were checked with kdecide on the statement, with a 900 s limit and MemoryMax 100G. Peak GiB is maxrss
KiB / 2^20 and can exceed the cap by shared file pages. Earlier runs with superseded settings (see the kfact.jsonl note)
agree. RCert.M3.NCheck and RCert.M3G.NCheck timed out at 900 s, and RCert.M3.NCheck at 3,600 s ran out of memory at
96 GiB after about 14 minutes.

The published record states two hand-built kernel tracks. `lean_kernel` (the U2/v3 bounds) took 10.3 CPU-hours, 1 h
35 min on 32 threads, not counting Mathlib (lean_kernel/README.md:46). `lean_u3g_kernel` (U3g/V4g) took 2,494
CPU-hours for its 7,871 pattern modules of 877-1,255 s each (README.md:301). In the native version,
`lake build Romanoff.Theorems` took 8 min 35 s on 8 cores, about 800 CPU-seconds for the 72 modules
(lean/README.md:79-80).

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
