# Tests of library v15

Library v15 (`6b378a8e`) adds one check to v14: the final theorem produced by the staged route must use only the
standard axioms. Its tests are the self-contained suite in `tests/kz/` (`study/gates/v15_tests.sh`, which adds
`StageAxioms` to the v14 suite). The suite was run with the v15 build on 14 toolchains and compared with the same suite
on the v14 build.

| directory | contents |
|---|---|
| `v15/<tc>/` | the suite with library v15, on 14 toolchains: each test's output (`.out`) and its difference from the expected output (`.exp.diff`) |
| `v14base/<tc>/` | the suite with library v14 on the 10 toolchains that `../v14_tests/` does not cover |
| `stage2/{v15,v14}/<tc>/` | the final `StageAxioms` test on all 14 toolchains, with v15 and with v14 (`study/gates/v15_stage2.sh`) |
| `../v15_builds/` | the build result of library v15 for each toolchain |
| `../v15_staged5/` | the five conversions through the staged route, run again with library v15 (fact files and logs) |

`study/gates/v15_compare_artifact.sh` compares the v15 outputs with the v14 ones (`../v14_tests/<tc>/` where it exists,
else `v14base/<tc>/`). It first normalizes the outputs as the test script does: times are masked, time and trace lines
are dropped, and `TypesRepro` is also compared on its verdict lines alone. The outputs agree on every toolchain, with
two exceptions: `StageAxioms`, which is new where the v14 run predates it, and two message lines of `TypesRepro` on the
nightly, whose verdict lines agree. All 28 runs of the final `StageAxioms` test give the expected output.

In `v15/` and `v14base/`, `StageAxioms.out` comes from the first version of the test, whose negative case used `sorry`.
Lean 4.27 prints the warning for `sorry` differently, so the final test (`tests/kz/StageAxioms.lean`, run in `stage2/`)
uses an axiom instead. The tests ran on a build of the v15 sources made before a one-line change to a comment; the
build of the final sources is byte-identical to it apart from Lake's trace files.
