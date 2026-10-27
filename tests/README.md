# Tests

`../run_tests.sh` runs every test file here against the library built in the parent directory and
compares the output of each `<T>.lean` that has a `<T>.expected` file next to it. The other test
files are run and reported with their exit code only; `AIStyleGoals.lean` and `MathlibSmoke.lean`
import Mathlib and are skipped.

`migrate_budget/` checks the per-fact budget and the slowdown limit of `ntrust migrate` on a small package:
`migrate_budget/run_test.sh NT_DIR TC WORK` builds it against the library in `NT_DIR` with toolchain `TC` in
the new directory `WORK` and prints PASS or FAIL per check. `../run_tests.sh` does not run it.

The expected outputs were produced with Lean v4.34.0. On other toolchains the output differs in these known
ways, all in Lean's own messages:

| toolchain | test | difference |
|---|---|---|
| v4.35.0-rc3, v4.35.0, nightly-2026-10-22 | `KernelFirstLite` | the error message of a failing `decide` is worded differently |
| v4.31.0 | `KernelFirstTest`, `PlatformCases` | axiom lists have no `Classical.choice` (in `KernelFirstTest` that of the fact that falls back to native evaluation, in `PlatformCases` those of the converted hash-set and hash-map facts) |
| nightly-2026-10-22 | `CastRetry`, `TypesRepro`, `KernelFirstTest`, `KernelFirstModule` | axiom lists have no `Classical.choice` |
