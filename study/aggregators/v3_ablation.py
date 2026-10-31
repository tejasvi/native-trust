#!/usr/bin/env python3
"""v3_ablation.py: the final run's ablation (Section 4.4) recounted from its result files. Each fact's verdict without the
transformations is its last row in study/results/v3/ablation/v3plain-<package>.ax.tsv, with v3plainr-<package>.ax.tsv (the
checks that ended in an error, re-run alone at 900 s and 48 GiB) laid over; facts inside definitions and instances and
modules that did not build are left out, as in study/results/v3/runs/sweeps/agg/v2/ablation.tsv. Prints, per package, the
facts re-run, those converted again and the verdicts of the others, then the totals.
usage (from the artifact's top directory): python3 -I -B study/aggregators/v3_ablation.py
"""
import collections
import glob

D = 'study/results/v3/ablation/'
last = {}
for f in sorted(glob.glob(D + 'v3plain-*.ax.tsv')) + sorted(glob.glob(D + 'v3plainr-*.ax.tsv')):
    for line in open(f, encoding='utf-8'):
        c = line.rstrip('\n').split('\t')
        if len(c) >= 7:
            last[(c[0].split('-', 1)[1], c[1], c[2])] = c
run, proved = collections.Counter(), collections.Counter()
other = collections.defaultdict(collections.Counter)
for (pkg, _, _), c in last.items():
    if c[5] == 'NOT_BUILT' or c[4] == 'True':
        continue
    run[pkg] += 1
    if c[5] == 'PROVED':
        proved[pkg] += 1
    else:
        other[pkg][f'{c[5]}/{c[6]}'] += 1
for pkg in sorted(run):
    rest = ', '.join(f'{k}={n}' for k, n in sorted(other[pkg].items()))
    print(f'{pkg}\tre-run {run[pkg]}\tconverted again {proved[pkg]}' + (f'\tnot converted: {rest}' if rest else ''))
r, p = sum(run.values()), sum(proved.values())
print(f'TOTAL\tre-run {r}\tconverted again {p}\tnot converted {r - p}')
