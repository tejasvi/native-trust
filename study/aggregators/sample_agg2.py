#!/usr/bin/env python3
"""Aggregate the random-sample runs (results/s_*.ax.tsv): per package, the last verdict of each native fact,
NOT_BUILT excluded; pooled, per-package mean and median, verdict and reason counts. Run as ntbuild on the box.
v2: --override PKG=RESULTS takes package PKG's facts from results/RESULTS.ax.tsv instead (re-runs with the patched
tool, e.g. FrederickPu_Zag=nt16-zag); unless --no-default-overrides, the two re-runs of lane V5 are used.
usage: sample_agg2.py [RESULTS_DIR] [--override PKG=RESULTS]... [--no-default-overrides]"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections, glob, os, statistics, sys
args = [a for a in sys.argv[1:]]
ov = {} if '--no-default-overrides' in args else {'FrederickPu_Zag': 'nt16-zag', 'BobDyLean_bobdylean_paper_artifact': 'nt16-bobdylean'}
for i, a in enumerate(args):
    if a == '--override':
        k, v = args[i + 1].split('=', 1); ov[k] = v
pos = [a for i, a in enumerate(args) if not a.startswith('--') and (i == 0 or args[i - 1] != '--override')]
R = pos[0] if pos else (NT_BOX + '/results')
pk = {}
used = {}
for f in sorted(glob.glob(os.path.join(R, 's_*.ax.tsv'))):
    name = os.path.basename(f)[2:-7]
    if name in ov and os.path.exists(os.path.join(R, ov[name] + '.ax.tsv')):
        used[name] = ov[name]
        f = os.path.join(R, ov[name] + '.ax.tsv')
    last = {}
    for l in open(f, errors='ignore'):
        c = l.rstrip('\n').split('\t')
        if len(c) >= 7:
            last[(c[1], c[2])] = c
    rows = [v for v in last.values() if v[5] != 'NOT_BUILT']
    nb = sum(1 for v in last.values() if v[5] == 'NOT_BUILT')
    pk[name] = (rows, nb)
withf = {k: v for k, v in pk.items() if v[0]}
tot = sum(len(v[0]) for v in withf.values()); pr = sum(sum(1 for r in v[0] if r[5] == 'PROVED') for v in withf.values())
rates = {k: sum(1 for r in v[0] if r[5] == 'PROVED') / len(v[0]) for k, v in withf.items()}
print('overrides used:', used)
print(f"result files={len(pk)} packages_with_facts={len(withf)} facts={tot} proved={pr} pooled={100 * pr / max(tot, 1):.1f}%")
if rates:
    print(f"per-package mean={100 * statistics.mean(rates.values()):.1f}% median={100 * statistics.median(rates.values()):.1f}%")
big = max(withf, key=lambda k: len(withf[k][0])) if withf else None
if big:
    t2 = tot - len(withf[big][0]); p2 = pr - sum(1 for r in withf[big][0] if r[5] == 'PROVED')
    print(f"largest={big} ({len(withf[big][0])} facts); pooled without it={100 * p2 / max(t2, 1):.1f}% ({p2}/{t2})")
print('verdicts', dict(collections.Counter(r[5] for v in withf.values() for r in v[0])))
print('reasons of non-proved', dict(collections.Counter((r[5], r[6]) for v in withf.values() for r in v[0] if r[5] != 'PROVED')))
for k in sorted(withf, key=lambda k: -len(withf[k][0])):
    rows, nb = withf[k]
    c = collections.Counter(r[5] for r in rows)
    print(f"  {k}\t{len(rows)}\t{c['PROVED']}\t{100 * rates[k]:.0f}%\t" + ' '.join(f"{a}={b}" for a, b in sorted(c.items()) if a != 'PROVED') + (f"\tNOT_BUILT={nb}" if nb else ''))
print('no facts:', ' '.join(sorted(k for k in pk if not pk[k][0])))
