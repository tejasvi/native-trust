# The final run

The corpus and the random sample of Section 4 were run again with the final library, the library at the top of this
artifact (manifest `6b378a8e`), with the per-fact driver of the baseline run (`study/drivers/m2_axioms5.py`;
`m2_repo4.py` for the six rs-mca sub-projects on Lean 4.28), the same facts, the same limits and the same heavy pass.
The baseline run is the study's run in `study/results/m2/` and `study/results/sample/`. The library was
built for each of the 26 toolchains that the packages pin (`study/library_versions/final_run_builds.tsv`). This
directory holds the per-fact results of every pass of that run and of the extensions run on its unconverted facts,
the logs of the facts that did not convert, the aggregation that gives the paper's numbers and tables, and the
records of the runs.

## Recomputing the numbers

From the artifact's top directory:

    python3 -I -B study/aggregators/v3_numbers.py study/aggregators study/results/v3/ax - - \
      --res-extra study/results/v3/pertheorem --res-extra study/results/v3/components/propsplit \
      --res-extra study/results/v3/components/options --res-extra study/results/v3/components/shards \
      --res-extra study/results/v3/components/addons --res-extra study/results/v3/components/bv_decide \
      --map study/aggregators/v3_map.tsv --axiom-index study/results/v3/axiom_index.tsv.gz \
      --logs study/results/v3/logs --study-m2 study/results/m2/ax --study-sample study/results/sample \
      --study-pt study/results/m2/pertheorem --check study/results/v3/agg
    python3 -I -B study/aggregators/v3_paper_numbers.py study/results/v3/agg -

The first command recomputes the aggregation and compares each of its ten outputs with the copy in `agg/`. It prints
one line per output and exits with status 0 when all of them are identical. To write the outputs instead, replace
the first `-` by a new directory and leave out `--check`. The second command prints the paper's macros
(`numbers_v3.tex`, the block between `% BEGIN v3 numbers` and `% END v3 numbers` in `paper/main.tex`) and the rows of
Tables 1, 2 and 3 (a), each after a line `== NAME`; `study/aggregators/v3_check_blocks.py` compares them with the paper's
generated blocks. From the result files, `v3_extensions.py` recounts Table 3 (b), `v3_ablation.py` the ablation,
`v3_copies.py` the well-founded copies, and `v3_options.py` the options and the shards (all in `study/aggregators/`).

## Passes and columns

Each fact belongs to a run `B` of the baseline run: a corpus package, an rs-mca sub-project or a sample package (`s_*`).
The final accounting reads these passes:

- **D**, the final library at the baseline run's protocol. `v3-B` is the default run (900 s and a 48 GiB address-space cap
  per fact). `v3r-B` re-runs alone the checks that were stopped by the memory limit their group of processes shared
  rather than by their own limits. The heavy pass (3,600 s and 96 GiB per fact) is `v3h-B` for the facts that ran out
  of memory, `v3h-B_t` for the time-outs, `v3h-B_b` for the `bv_decide` time-outs, and `v3h-B_r` for the `_t` and
  `_b` checks stopped by their group's limit. A fact converted in any D pass counts as converted; otherwise its
  verdict is its last row that was not stopped by its group's limit.
- **G**, general add-ons: the `bv_decide` pipeline (`components/bv_decide/v3bvs-*`) and the `@[csimp]` add-on
  (`components/addons/v3a-csimp_*`).
- **P**, the option `propSplit` (`components/propsplit/v3p-*`).
- **O**, the other options (`components/options/v3o-*`: `stage`, `csimp` and `propSplit` together, with up to 16
  parts) and sharding (`components/shards/v3s-*`).
- **K**, package add-ons (`components/addons/v3a-*`, `v3b-*`).

Each column includes the ones before it. `study/aggregators/v3_map.tsv` names the files of G and K and the shard
files, and `v3_mk_map.sh` wrote its shard lines; `v3p-B` and `v3o-B` are found by name. The other files in
`components/`, and `ablation/` and `nocap/`, are cited in the text but are not columns.

## Contents

| path | contents |
|---|---|
| `ax/` | The D passes: `v3-B`, `v3r-B` and `v3h-B[_t\|_b\|_r]` (`.ax.tsv`), one line per fact in the columns of `study/results/m2/ax/` (package, module, axiom, tactic, inner, verdict, reason, kernel ms, peak memory in KiB, seconds, blockers and trace). |
| `pertheorem/` | The six rs-mca sub-projects on Lean 4.28, per theorem (`m2_repo4.py`): `v3-`, `v3r-` and `v3h-rs-mca-*.tsv`. |
| `components/propsplit/`, `components/options/` | The columns P and O. |
| `components/shards/` | Sharded checks: `v3s-*.ax.tsv` (in the options column) and, per fact, its pieces, times, peak memory and the axioms of the combined theorem (`v3s-*.figs.tsv`); `v3s_totals_v1.tsv`, per package. `v3spilot-*` are the probes of the first piece of 8 facts each in BerryEsseen's covers, sections 6-9 of the author's package and minidregg; they are not counted. The script that writes the shard results first labeled a fact that fails on a native fact nested inside it NOT_RUN, because Lean exits with status 0 after that message; the shipped files carry the corrected label (FAILED, reason `nested_native_fact`). |
| `components/option_controls/` | The facts that the options converted, checked again with one option alone: `v3oc-` (`csimp`), `v3os-` (`stage`), `v3op-` (`propSplit`) and `v3o16-` (16 parts). `v3oh-trainverify` gives the options 3,000 s per fact, and `v3oz-s_zcash_ironwood` runs them with a shared staging module (`study/results/after/options/c22z/PrepZcash.lean`). |
| `components/addons/`, `components/bv_decide/` | The columns K and G. |
| `ablation/` | The default run's conversions outside definitions and instances, re-run with the well-founded replacement and splitting switched off (`v3plain-*`), and the checks of these runs that ended in an error, re-run alone at 900 s and 48 GiB (`v3plainr-*`; most of them had been stopped by their group's memory limit). |
| `nocap/` | Facts of Strata labeled blocked (a sample of 20), re-run with the cap switched off. |
| `selections/` | The facts that later runs took: `v3u-*`, the facts that no D pass converted (the input of the extensions); `v3msel-*`, the default run's rows followed by the re-runs alone, from which the ablation took BerryEsseen's and longfellow-zk's conversions; `v3ocsel-*`, `v3ohsel-*` and `v3ozsel-*`, the inputs of the controls. |
| `logs/` | Check logs, gzipped: every D-pass log of each fact not converted (`logs/<run dir>/<log name>.gz`, which `v3_numbers.py` finds through `axiom_index.tsv.gz`), the logs of the converted facts that made well-founded copies (Section 4.6: those of the default run and its re-runs alone, and BE4's of the heavy pass), the per-theorem driver's logs of rs-mca (`logs/v3*-rs-mca-*/`, every pass: the check of each theorem, the listing of each module's native theorems and the run log), the option runs' logs of the four aks and sorting-network facts on which staging stops the process (`logs/v3o-*/`), and the logs of the run without the cap. The shard logs are in `logs/shard/` (no limit on the number of modules), `logs/shard_n64/` (at most 64 modules) and `logs/shard_probe/` (the probes), one directory per fact with the modules' header and the logs of the pieces, of the combining module and of the axiom check. `logs/INDEX.tsv` gives the fact, the pass and the reason for each log. |
| `axiom_index.tsv.gz` | Every fact of the default runs with its index in its module's listing (base, module, axiom, index), which gives the name of its check log. |
| `proved_lines.tsv.gz` | The `PROVED` line of every check log of the D passes (run directory, log name, line; each log prints the line twice, and one copy is kept). It gives the copies, the accessibility fallback (`acc_fallback`) and the times of every conversion, including those whose logs are not kept. |
| `agg/` | The outputs of the two commands above: `summary.txt`, `per_package.tsv`, `verdicts_D.tsv`, `classes_D.tsv`, `facts_not_converted_D.tsv` (class, blockers, pass, and what the log says stopped the kernel), `facts_D.tsv` (every fact with its final D row, its columns and the baseline run's verdict), `regress_D.tsv`, `harness_D.tsv` (rows stopped by a group's limit that are left in the final accounting: none), `factlist_diff.tsv` (the fact lists against the baseline run's) and `map_used.tsv`; then `numbers_v3.tex`, `table1_v3.tex`, `table2_v3.tex`, `tableext_v3.tex` and `report_v3.txt`. |
| `runs/lanes/` | The default runs' lane logs (start and end of each package and the driver's arguments, among them the library root) and the driver's output per package (`out/`). The lane files are `study/drivers/lanes/v3_*.tsv`, run by `study/drivers/m2_lane_v3.sh` and `m2_lane_repo_v3.sh`. |
| `runs/passes/` | The later D passes and the shards: the queues of items (`queue_v*.tsv`: item, kind, run, default run, package, library root, processes, memory per process, seconds and memory per fact), the selection of each item (`sel/`: `.keys` lists the facts, `.re` is the driver's pattern and `.summary` gives the counts by reason; `sel/v3r-*` and `sel/v3hr-*` list the checks stopped by their group's limit and re-run alone), the driver outputs (`out/`), the search paths (`lp/`), the shard lists (`shard_lists/`), `final_packages.tsv`, and the BerryEsseen items run on a second machine of the same type (`clone/`). The runner that scheduled these items on the shared machine is not included. |
| `runs/opt/` | The runs of the options and of the add-ons: scripts and lists (`bin/`), logs (`logs/`, and `logs_clone_*` for the items run on the second machine), and a measurement of minidregg's circuit sizes (`fail116/`). |
| `runs/addons/` | The build logs of the add-ons. Their sources are files of this artifact: `addons/bob/`, `addons/fcprimes/`, `addons/primes/PrattCert.lean`, `addons/longfellow/`, `addons/minidregg/`, `addons/regex/`, `addons/strata/`, `study/results/after/general/csimp/NTMathlibCsimp.lean` (the `@[csimp]` add-on), `study/remedies/clean/KernelFactsClean.lean` and `study/results/after/options/c22z/PrepZcash.lean`. |
| `runs/berry_addon/` | BerryEsseen's package add-ons, run on the second machine: per cover, the generated modules with their logs, error output and times (`covers/<tag>/`); the logs of the scheduler and of the tokenizer pass (`logs/`); per cover the total and the critical path of its processes (`cover_times_v1.txt`, written by `scripts/berry_summary_v1.sh`); and the scripts. The add-ons' sources are `addons/berryesseen/` and `addons/berryesseen_parse_once/`. |
| `runs/berry_check/` | Builds of the BerryEsseen add-on sources against the final library (logs). |
| `runs/sweeps/` | The `bv_decide` pipeline's runs (`bvs/`: per-fact modules and logs, results and axiom checks), the scripts of the pipeline and of the ablation and label-check re-runs (`scripts/`), their tables (`agg/`, `agg/v2/`: `ablation.tsv`, `wf.tsv`, `nocap.tsv`, `copies_*.tsv`, `modof*.tsv`) and the names of the copied definitions (`agg/v2/core_lib_names.txt`: those of core and Mathlib; `all_copied_names.txt`, `be4_copied.txt`), and BerryEsseen's BE4 checked without the well-founded replacement (`be4/`, run by `scripts/v3ms_be4_v1.sh`). |
| `runs/sizes/` | `certificate_files.tsv`: the certificate files that the facts of aks and sorting-network read, with their size, the checkout commit and the module and definition that read each, as listed on the study machine. |
| `runs/wf_off/` | rs-mca's `MomentToMax.PTEClusterPacking.champion_packingStats`, which the per-theorem driver converted in the heavy pass, checked again without the well-founded replacement (Section 4.6): the script, with the command of the baseline run's ablation (`study/results/ablation/rs-mca-moment_to_max/`) and the final library's build for Lean 4.28, and its output, in which the kernel is stuck at `WellFounded.fix` through `List.mergeSort` and `List.merge`. |

In the records, the names of working directories on the machines are replaced by neutral ones (`passes`, `sweeps`,
`clone`), host names are removed, and the scripts refer to the build account's home directory through `NT_BOX`, as
elsewhere in this artifact. Scripts that only started, gated or guarded jobs on the shared machines are not
included.
