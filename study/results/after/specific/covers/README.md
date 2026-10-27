# BerryEsseen: covers parsed once

These are the results of the add-on in `addons/berryesseen_parse_once/`; its README describes the method, the build and
the checks.

- `<tag>/F2_<tag>.log`: the final check of each cover, with the PROVED line for its fact and `rc=0`.
  `study/aggregators/after_table.py` counts these facts as converted.
- `berry-esseen-covers.ax.tsv`: one line per converted fact (259), in the same columns as the driver results
  (`../../../m2/ax/`). Columns 8 and 10 give the kernel time in milliseconds and the elapsed time in seconds, summed
  over all processes of the cover, and column 9 gives the largest peak memory among them, in KiB. Column 12 gives the
  final theorem's name, its number of leaves and its axioms.
- `RESULTS_covers.md`: one row per cover, with its leaves, elapsed time in seconds, peak memory in GiB, the parse-once
  step, the median and largest leaf times, and the axioms of the final theorem.
- `checks/`: the logs of the independent checks of nine exports. Each export has a one-line `.chk` summary and the
  checkers' outputs. `K_BE3.lean` is the module exported for the BE3 check.

The time of a cover is the sum of the elapsed times of all its lean processes (tree, parse, leaf modules, assembly
and final check); each process ran on one thread (`-j1`). `study/checks/be_cost.py` adds them up for all of
BerryEsseen's conversions, together with the times of the other mechanisms.
