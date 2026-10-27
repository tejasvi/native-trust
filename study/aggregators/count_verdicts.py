#!/usr/bin/env python3
"""Verdict counts of per-fact result files (*.ax.tsv), with the aggregators' counting rules.

usage: python3 -I study/aggregators/count_verdicts.py FILE.ax.tsv [FILE.ax.tsv ...]

For each file, and for all files together: the facts (the last line per (package, module, axiom) counts; NOT_BUILT
lines left out), verdict counts and reasons, split into facts outside and inside definitions (column 5, inner),
and the range of the wall-clock seconds (column 10) per verdict.
Columns: package, module, axiom, tactic, inner, verdict, reason, kernel_ms, maxrss_kb, secs, blockers, trace.
"""
import collections
import sys


def load(path):
    last = {}
    for line in open(path, errors='ignore'):
        c = line.rstrip('\n').split('\t')
        if len(c) < 7:
            continue
        c += [''] * (12 - len(c))
        last[(c[0], c[1], c[2])] = c
    return [c for c in last.values() if c[5] != 'NOT_BUILT']


def report(name, rows):
    for label, part in (('outer', [c for c in rows if c[4] != 'True']), ('inner', [c for c in rows if c[4] == 'True'])):
        v = collections.Counter(c[5] for c in part)
        r = collections.Counter(f"{c[5]}/{c[6]}" for c in part if c[5] != 'PROVED')
        secs = collections.defaultdict(list)
        for c in part:
            if c[9].isdigit():
                secs[c[5]].append(int(c[9]))
        rng = '; '.join(f"{k} {min(s)}-{max(s)} s" for k, s in sorted(secs.items()))
        print(f"{name}\t{label}\tfacts={len(part)}\t" + ' '.join(f"{k}={n}" for k, n in sorted(v.items())) +
              (f"\tnot proved: {' '.join(f'{k}={n}' for k, n in sorted(r.items()))}" if r else '') +
              (f"\tsecs: {rng}" if rng else ''))


allrows = []
for p in sys.argv[1:]:
    rows = load(p)
    allrows += rows
    report(p.rsplit('/', 1)[-1], rows)
if len(sys.argv) > 2:
    report('ALL', allrows)
