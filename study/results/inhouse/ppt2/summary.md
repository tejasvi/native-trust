# PPT2 paper 2 (deposit v5)

The native facts are the distinct `native_decide` axioms in the theorem closures that the deposit lists per theorem
(`lean/integration_v3/build/class/theorems_*.tsv`, made with Lean's collectAxioms). There are 751 in core and 1,039 in
rows_a. The paper cites 998 NATIVE theorems, 606 in core and 392 in rows_a. The deposit counts 1,000, because it
includes its 34 composition lines. The closures of the cited theorems hold 594 core facts and 670 rows_a facts.

In core, all 751 facts were run in pass 1 (900 s, 48 GiB), and a random 10 of its memory failures were run again at
3,600 s and 96 GiB. In rows_a, pass 1 ran the 670 cited-closure facts first and stopped at the agreed budget of 37.5
box core-hours for builds and pass 1 together, so only part of rows_a was run. The heavy sample re-ran 10 randomly
chosen rows_a memory failures. ppt2_counts.txt has the exact run and not-run counts.

The first build ran only the default `lake build` targets. The deposit README (README.md:217-225) builds index
targets next, so the 54 core modules and 192 rows_a modules behind them were built in a second step before their
facts were run (core 226 s wall, rows_a 2,277 s wall and 13,831 s user).

At theorem level, ppt2_theorems.tsv has one line per NATIVE theorem, with its native axioms and status. A theorem is
CONVERTED when every native axiom in its closure ended PROVED, so it now has a kernel-checked proof. It is
NOT_CONVERTED when one of those axioms was run and did not end PROVED, and UNCHECKED when one of them was not run.
ppt2_counts.txt lists the rows of Table A.1 whose cited native theorems are all converted (the line "rows with native
cited theorems: 165; all of them converted: 86: R001 ...").

There is no hand-built kernel track. The authors redid part of the checks in the kernel alone (`PPT2Cert/Kernel`, all
KERNEL), which does not replace the native facts.

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
