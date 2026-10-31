# The study: scripts and results

`../results_index.tsv` lists every number in the paper, together with the files backing it and the command
recomputing it from those files. The commands run from the artifact's top directory with `python3 -I`
(standard library only) or standard shell tools, and need no Lean. The columns are id, where (the section and
line of `paper/main.tex`), claim, value as printed, files, command, check, status and notes. The check column
lists strings contained in the command's output, in which `\t` stands for a tab and ` && ` separates two
strings. The status is OK when the command's output contains every check string, PARTIAL when the files back
part of the claim, CHECK when the value computed from the files differs from the printed value (the notes say
why), TODO when a backing file is not in the artifact, EXTERNAL for a value cited from outside, and NOTE for a
setting or a restatement.

## Scripts

These are the scripts used for the runs, which were made on cloud machines of one type under a dedicated build account.
In this copy the scripts refer to that account's home directory through the variable `NT_BOX`, which defaults
to the original directory; setting it lets them run under another directory.

| directory | contents |
|---|---|
| `drivers/` | `m2_axioms*.py` (versions 1-5) is the per-fact driver, which runs one native fact per Lean process under a time and memory limit. `m2_repo*.py` is the earlier per-theorem driver, used for the packages on Lean 4.28. `m2_lane*.sh` runs a lane file. Each lane file `lanes/*.tsv` lists the run name, the package directory and the arguments for its runs. `lanes/heavy_pass.tsv` lists the heavy-pass command lines (3,600 s, 96 GiB). `sample_clone.sh` clones and classifies the sampled repositories. `m2_lane_v3.sh` and `m2_lane_repo_v3.sh` run the final run's lane files (`lanes/v3_*.tsv`) with the same drivers. |
| `aggregators/` | `m2_aggregate_ax.py` computes the per-package results and failure classes, and `m2_aggregate2.py` computes the per-theorem results. `plain_agg.py` aggregates the ablation. `sample_agg2.py` and `sample_cls.py` aggregate the random sample. `wf_facts.py` lists the facts whose evaluation made well-founded copies. `migrate_table.py` builds the `ntrust migrate` table. `removal_sample_tables.py` builds the removal tables of the random sample, for `ntrust migrate` and for the one-import switch. `paper_numbers.py` computes the numbers of the baseline run (the study) as reported in Tables 1 and 2 and Sections 4.1-4.3. `count_verdicts.py` counts the verdicts in per-fact result files using the aggregator rules. `bvd_213.py` covers every `bv_decide` fact of the corpus and the sample, that is, the sweep and the nine facts not converted by the sweep. It checks each value of `final9.tsv` and `groups.tsv` against the logs cited for the value, and it evaluates the sweep checks, which were run in a fresh process. `after_table.py` counts the facts converted per package in the study and in the work that followed it, which Section 4.7 ("Options and add-ons") cites for the baseline run's failures; it groups the later conversions by library runs, general add-ons, opt-in options and package-specific add-ons. `bvk_tables.py` builds the `bv_kdecide` tables in `addons/bvs/README.md`. `v3_numbers.py` computes the final run's results from its result files with the counting rules of the baseline run, and `v3_paper_numbers.py` turns them into the paper's numbers and the rows of Tables 1, 2 and 3 (a), which `v3_check_blocks.py` compares with the paper; `v3_map.tsv`, written by `v3_mk_map.sh`, names the result files of the extensions. `v3_extensions.py`, `v3_ablation.py`, `v3_copies.py` and `v3_options.py` recount Table 3 (b), the ablation, the well-founded copies and the options and shards from the result files (see `results/v3/README.md`). |
| `checks/` | `stmt_check.py` and `stmt_check2.py` check the statement identity and the axioms of kernel supplements. `supp_check2.py` runs nanoda and con-ron on every supplement module. `recheck2.py` and `recheck_all.sh` run the sampled re-checks. `be_literal_sizes.py` measures the sizes of BerryEsseen's certificate literals, and `be_cost.py` adds up the time of BerryEsseen's conversions by mechanism. |
| `gates/` | `v*_gates.sh` run the regression gates before each library change, and `v*_compare.py` compare their results with the baseline runs. `v14_compare_v2.py` differs from `v14_compare.py` only for ninegates, which it reads from the run over all of the package's facts. `v3_nowf.sh` is the no-WF lane, `v7_fix3.sh` tests the fuel-route retry, and `v9_casts_check.sh` is the cast-fact check. `v11_tests_v2.sh` is the test runner used to produce the expected outputs. `v13_tests.sh` and `v14_tests.sh` are its copies for library v13 and v14. |
| `builds/` | `nt_fix*_build.sh` build the library versions used in the runs. `v3_build_one_v1.sh` and `v3_build_many_v1.sh` build the final library for the toolchains that `nt_fix14_build_one.sh` had not built. |
| `migrate/` | `ntrust_migrate.py` is the source rewriter of the paper's Tables 4 and 5, and `patches/` contains its rewrites. |
| `sample/` | `frame585.tsv` lists the 585 repositories returned by GitHub code search for `native_decide language:Lean` (October 2026). `excluded35.tsv` lists the 35 repositories examined or inspected before the draw and gives the reason for every exclusion. `draw_sample.py` performs the draw (seed 20261023) and reproduces `sample585.txt`, which lists the 70 repositories drawn, in order. |
| `corpus/` | `commits.tsv` lists the commit of each corpus repository and its date, and `toolchains.tsv` lists each package's toolchain file. |
| `remedies/` | `clean/KernelFactsClean.lean` contains kernel-checked primality proofs (by `norm_num`) for the `Fact (Nat.Prime p)` instances of Verified-zkEVM/clean and registers them with `@[kernel_fact]`. |
| `library_versions/` | The library sources of every version cited in the paper or in the run records, in one directory per manifest (see the README there). |
| `addon_versions/` | The `bv_decide` add-on as it was for the paper's runs (see the README there). |

## Results

Each analysis has its own directory, which contains the files read by its command.

| directory | contents |
|---|---|
| `results/v3/` | The final run with the final library (Section 4): the per-fact results of every pass and of the extensions run on its unconverted facts, the logs of the facts not converted, the aggregation behind the paper's numbers and tables, and the records of the runs (see the README there). |
| `results/m2/ax/` | Per-fact results of the study run (`*.ax.tsv`), one line per native fact, in the columns package, module, axiom, tactic, inner, verdict, reason, kernel ms, peak memory in KiB, seconds, blockers and trace. Per-theorem results of the same run (`*.tsv`). |
| `results/m2/` | The aggregator output (`aggregate.txt`), and `facts_not_proved.tsv`, which gives the class and the blocking constants of every fact not converted, as read from the per-fact logs. |
| `results/ablation/` | Re-runs of every converted fact with the transformations off (`*-plain`), and the runs used for the comparison. |
| `results/validation/` | Uncapped re-runs of the blocked facts (`*-nocap`), samples run without the transformations (`*-base`) and runs without the well-founded replacement (`*-nowf`). |
| `results/current_tool/` | Re-runs with the fuel route and its retry (`*-nt18`, `retry-*`), and the heavy pass over formal-conjectures. |
| `results/sample/` | The random sample, one file per package (`s_*`), and the class table of the drawn repositories (`sample585_classes.tsv`). |
| `results/supplements/` | For each of three packages, the kernel supplements written by `lake exe ntrust` (`Kernel/`), the driver's report, and the outputs of the statement check (`stmt/`) and of nanoda and con-ron (`check2/`). |
| `results/recheck/`, `results/recheck2/` | Sampled re-checks per package, that is, the outputs of nanoda and con-ron and their summaries. |
| `results/qec/` | The conversion of a published theorem (61 facts) and its checks. |
| `results/inhouse/` | NativeTrust on the author's published results that use `native_decide`, one directory per result, with the costs of the hand-built kernel versions as stated in their records (see the README there). |
| `results/paper_example/` | The introduction's example: `Ex.lean` and its unedited output `Ex.out` (`lake env lean`, local build, Lean v4.35.0-rc3, 2026-10-28). |
| `results/migrate/` | The `ntrust migrate` runs without limits, one `summary.json` per package, and the table built from them by `migrate_table.py`. The runs with the default limits on library v14 are in `v14_defaults/`, and their table is `study6_v14.tsv`. |
| `results/nightly/` | The fuel-route tests on a Lean nightly containing core PR #14892. |
| `results/bv_decide/` | Files for the `bv_decide` route of Section 7, in the subdirectories and files below. |
| `results/bv_decide/logs/` | The goals in Table 8, ByteDecomposition compiled as four modules in parallel, and nanoda's check of ByteDecomposition. |
| `results/bv_decide/sweep/final_per_fact.tsv` | One line for every `bv_decide` fact of the corpus and the sample, giving the verdicts of the bitmask checker and of the bit-blaster route. |
| `results/bv_decide/sweep/checks/` | The axiom and statement checks of these facts, run in a fresh process, and nanoda's check of a sample of them. |
| `results/bv_decide/final9.tsv` | The nine facts not converted by the sweep; every value is paired with the log that records it. |
| `results/bv_decide/groups.tsv` | The facts whose rebuilt declarations use facts from other modules or packages and which were converted together in one module, and the logs recording each value. |
| `results/bv_decide/logs7/` | The later runs cited in `final9.tsv` and `groups.tsv`: shards, a split first pass, acceptance checks with nanoda, a run in which nanoda rejects a native original, the axiom audit of the soundness proofs on three Lean versions, a goal with 1.18 million clauses, and the conversions made together (`groups/`). |
| `results/bv_decide/core_pipeline/` | Core's pipeline on a 312-node goal. |
| `results/bv_decide/dedep_cmp/` | The goal `x * 3 = x + x + x` at widths 4 to 1,024. |
| `results/bv_decide/tactic/` | The runs of `bv_kdecide` reported in `addons/bvs/README.md`, and an index of the evidence. |
| `results/after/` | Runs after the study, read by `after_table.py`, in the subdirectories and files below. |
| `results/after/library/runs/` | Per-fact runs of library versions v8 to v14: the re-runs of the facts that failed for resources, the runs of three retries, and the regression gates. The three retries are the cast retry, the string retry for iterator-based string functions and the word-size case split. |
| `results/after/library/highcap/` | Re-runs of the facts that have a piece above 48 GiB, for up to 3,600 s. |
| `results/after/library/types/` | Runs of the facts blocked by copies in types. |
| `results/after/library/shards/` | Facts proved in pieces in separate modules. |
| `results/after/library/shard_conversions.tsv` | An earlier pass over the resource failures. |
| `results/after/library/strings/` | The status, cause and evidence for each of the 42 iterator-string facts outside BerryEsseen, cedar-spec and the author's own package. |
| `results/after/library/casts_census/` | A census of the cast facts in formal-conjectures. |
| `results/after/library/logs/` | The per-fact logs of the Strata run on library v11. |
| `results/after/general/` | Runs with the csimp add-on. |
| `results/after/options/` | Single-fact runs of library v13 with the opt-in options, and the list of the facts that convert only with these options. |
| `results/after/resources/` | The final numbers of the resource re-runs on library v8. For the 80 facts with large values, it also gives their causes, their sizes and the options that convert some of them. |
| `results/after/specific/` | Runs of BerryEsseen with its tokenizer add-on and with its covers parsed once, of BobDyLean with and without NTBobDeq, and of the other package add-ons. |
| `results/gates/v13_tests/`, `results/gates/v14_tests/` | Outputs from the library's self-contained tests, one directory per toolchain (`*.out`), and their differences from the expected outputs (`*.exp.diff`). |
| `results/gates/v13_tests/rerun_*.log` | A second run of the v13 tests on three toolchains. |
| `results/gates/v14_tests/all.log` | The log of the v14 test run. |
| `results/gates/results/` | Regression gate runs for library v8 to v11, and the baseline runs against which they are compared. |
| `results/kernel_first/` | Runs of the one-import switch (`KernelFirst` and `KernelFirstLite`) on lido-srv3, on codegraff as published and with its six structure literals fixed, and on the 10 largest cvc5/logos modules. |
| `results/kernel_first/linter-overhead/` | A measurement of the linter's overhead. |
| `results/removal_sample/` | Removal runs on the random sample of 24 packages, tabulated by `aggregators/removal_sample_tables.py`. |
| `results/removal_sample/runs/mig/` | Each package's `ntrust migrate` run (`summary.json`, `plan.json` and the axiom censuses), and the runs of the one-import switch (`kf-*`). |
| `results/removal_sample/results/` | The per-fact runs of these packages and their re-runs on library v8. |
| `results/removal_sample/budget_table.md` | The results of `migrate` with the per-fact budget and the slowdown limit. |
| `results/removal_sample/runs/tools/` | The scripts that built `budget_table.md` from the summaries in `runs/mig/` (`p_*`, `b*_*` and `v14_*`). |
| `results/berryesseen_literals.tsv` | The size of every string literal in BerryEsseen's cover data modules. |
