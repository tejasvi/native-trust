# Library versions behind the runs

This directory holds the library sources (module files, root module, Lake file, toolchain file; no builds) of every
version whose source manifest is cited in the paper or in the run records. Each directory is named by the first 8 hex
digits of its manifest. The manifest is defined as in the paper: the SHA-256 of the per-file SHA-256 lines of the
library and Lake files, sorted by path. From a version's directory:

    find NativeTrust NativeTrust.lean lakefile.toml lean-toolchain -type f \( -name '*.lean' -o -name '*.toml' \
      -o -name lean-toolchain \) | LC_ALL=C sort | xargs sha256sum | sha256sum

| manifest | version | used by | how the sources were found |
|---|---|---|---|
| `6b378a8e…b3b6` | library v15: v14 + a check that the final theorem produced by the staged route uses only the standard axioms, as the theorems produced by the other routes do (`Kernel`) | the tests on 14 toolchains and the re-run of the five staged conversions; the library at the top of this artifact | the library at the top of this artifact |
| `918ae06c…4b26` | library v14 (box builds `nt_fix13`): v13 + memory fixes for the retries of iterator-string facts (`Copy`, `Kernel`, `Param`), the word-size case split for terms that reach `System.Platform.numBits` (`Kernel`, `Linter`, `Param`) and a per-fact budget and a slowdown limit for `ntrust migrate` (`Driver/Migrate.lean`) | gates `v14-*`, `v14c-*`, `v14s-*` and the tests (`study/gates/v14_tests.sh`); the v14 run of minidregg's three accessibility-fallback facts (`study/results/after/library/types/v14-miniacc/`) | backup of the module directory taken at 2026-10-25 17:24 UTC, just before the v15 change; its root module is unchanged |
| `19a2dbb3…09e7` | library v13 (box builds `nt_fix12`): v12 + staged evaluation and `@[csimp]` replacements in the kernel (opt-in: `stage := true`, `csimp := true`; `NativeTrust/Reify.lean`) | gates `v13-*`, `v13c-*`, `v13s-*` and the tests (`study/gates/v13_tests.sh`); the runs with opt-in options (`study/results/after/options/`, build `nt22`: the same library modules, see `nt22_sources.sha256` there) | backup of the module directory taken at 2026-10-25 12:01 UTC, just before the v14 change; its root module is unchanged |
| `72639b93…0d44` | library v12 (`nt_fix11`) | gates `v12-*`, `v12c-*`, `v12s-*`; the csimp add-on's runs and controls | backup of the module directory taken at 2026-10-24 21:41 UTC, just before the v13 change, with the root module at that time |
| `c35df73b…0265` | library v11 (`nt_fix10`): v10 + iterator-based string functions (`StrLib`, `@[kernel_fold]`) and `KernelFirstLite`, the string replacements applied in the first attempt; not adopted | gates `v11-*`, `v11c-*`, `v11s-*`: its Strata run lost 32 of 66 facts to time-outs (per-fact logs in `study/results/after/library/logs/v11-strata/`) | the sources of the box build (`nt_fix10/src`: modules, root module, Lake file) with the work tree's toolchain file; no manifest was recorded for v11 when it was built, so this one is computed from these files |
| `61dc5f97…8355` | library v10 (`nt_fix9`): v9 + copies in types | gates `v10-*`, `v10c-*` | backup of the module directory taken at 2026-10-24 08:19 UTC, which also holds the root module at that time |
| `9f92c396…8ea4` | library v9 (`nt_fix8`): v8 + the cast retry | gates `v9-*`, the cast runs `v9c-*` | backup of the module directory taken at 07:28 UTC, with the root module at that time |
| `9011ea48…6995` | library v8 (`nt_fix7`) | gates `v8-*`; the re-runs `v8r-*`, `v8rp-*` and the shards of the resource failures; the removal runs on the random sample; BerryEsseen with its tokenizer add-on and its covers parsed once | the complete v8 tree that was copied to the box |
| `e839bc05…0bbc` | `727e381b` + the one-import switch and the linter (`nt_fix5`) | with `727e381b`: re-runs of cvc5/logos, Strata and the 15 well-founded formal-conjectures facts (Appendix B) | backup of the module directory taken at 02:14 UTC; root module as saved with the next backup (03:15 UTC), which has the same content as the root module of `727e381b` |
| `727e381b…7147` | `649b14e3` + the restoration of the environment after a failed attempt (2026-10-24 00:01 UTC) | as `e839bc05` | the complete work copy of that change |
| `649b14e3…2045` | the fuel route with its retry (`nt_fix3`) | the final runs of cvc5/logos, Strata and formal-conjectures (Appendix B) | backup of the module directory taken at 00:01 UTC, just before the next change; root module of the work copy made from the same tree a minute later |
| `0d9bca14…1b8b` | the work build of the copies in types (box build `nt_final3`): v8 + copies that keep types | the copies-in-types runs `wt-final3-*` (Zag 3, minidregg 1, BobDyLean 12 with `NTBobDeq`) | the work tree of that change, which matches the per-file digests recorded with it at 2026-10-24 04:51 UTC |
| `b0da4454…0e24` | the fuel route without the retry (box builds `nt14`) | the supplements, the sampled re-checks, the ablation and the random sample | its seven library modules only (see below) |

Where a backup holds only the module directory (and the root module), `lakefile.toml` and `lean-toolchain`
(`leanprover/lean4:v4.35.0-rc3`) come from the library's work tree; both have the same content in every copy from
2026-10-23 20:53 UTC to the final version. Every manifest above is recomputed from the files in this directory
(`results_index.tsv`, row RP2).

One manifest, `b0da4454…0e24`, cannot be recomputed. Its seven library modules (`b0da4454/NativeTrust/`) come from a backup of the
module directory taken just before the patch that added the retry (2026-10-23 21:44 UTC); the box build copies of
`nt14` hold the same seven modules. The root module and the Lake files used for that build were not kept: no combination of
the modules with the surviving root modules, Lake files and toolchain files gives `b0da4454`. The same method
reproduces the manifest recorded right after that patch (`67ba4e72…0b88`).
