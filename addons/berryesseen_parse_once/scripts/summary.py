#!/usr/bin/env python3
"""Summary of BerryOpt conversions from results/RESULTS_covers.md (run anywhere: python3 summary.py RESULTS_covers.md).
Per family: facts converted, leaves, CPU-h, CPU-h per fact, s per leaf, max peak GB; axioms check."""
import sys, collections
rows = []
for l in open(sys.argv[1]):
    if not l.startswith('| ') or l.startswith('| cover') :
        continue
    c = [x.strip() for x in l.strip().strip('|').split('|')]
    rows.append(c)
agg = collections.defaultdict(lambda: [0, 0, 0.0, 0.0])
bad_ax = []
notconv = []
for c in rows:
    tag, mod, conv, leaves, done, cpu, peak, ps, pg, lmed, lmax, ax, chars = c[:13]
    if conv != 'yes':
        notconv.append((tag, conv, done, leaves)); continue
    fam = {'C': 'Small', 'S': 'Small', 'D': 'DW', 'B': 'BE'}[tag[0]]
    a = agg[fam]; a[0] += 1; a[1] += int(leaves); a[2] += float(cpu); a[3] = max(a[3], float(peak))
    if ax != 'propext, Classical.choice, Quot.sound':
        bad_ax.append(tag)
tot = [0, 0, 0.0, 0.0]
for fam in ('Small', 'DW', 'BE'):
    if fam not in agg: continue
    n, lv, cpu, pk = agg[fam]
    tot[0] += n; tot[1] += lv; tot[2] += cpu; tot[3] = max(tot[3], pk)
    print(f'{fam:5s} facts={n:3d} leaves={lv:5d} CPU-h={cpu/3600:6.1f} per-fact={cpu/3600/n:5.2f} s/leaf={cpu/lv:5.0f} peak={pk:.1f} GB')
print(f'TOTAL facts={tot[0]} leaves={tot[1]} CPU-h={tot[2]/3600:.1f} peak={tot[3]:.1f} GB')
print('finals with other axioms:', bad_ax or 'none')
print('not converted:', notconv or 'none')
