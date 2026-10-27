# thrackle 78a v3

NativeTrust v15 converted none of the 3 native facts it checked.

The 23 facts read certificate data through `load_cert_chunk`, from 5.4 MB to 295 MB per fact and 0.76 GB per DB fact.
The checks used kdecide on the statement (900 s, MemoryMax 100G). V4 and U15, the two facts with the smallest
certificates (5.47 and 5.40 MB, copied with the sha256 values in T78Data), ran out of memory after 324-325 s. They were
checked with `lake env lean`, because `lake build` asks for the whole precompiled T78Data library, whose other data
files are not on the study machine. TH233 needs no data file, but it is blocked. Its oracle `BM.bmOrcKR` reaches the
`partial` functions `BM.xLoop`, `sLoop`, `edgeLoop` and `fillLoop`, which the kernel cannot unfold.

There is no hand-built kernel track. In the native version, building the 23 facts re-runs every search of the checker,
which takes about 2,300-2,400 process-hours (README.md:288).

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
