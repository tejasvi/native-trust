#!/usr/bin/env python3
"""Failure classes of the random sample (results/s_*.ax.tsv), last verdict per fact, NOT_BUILT excluded, with the same
--override PKG=RESULTS handling as sample_agg2.py (no default overrides). Classes as in the 10-24 interim table:
resources = ERROR/TIMEOUT; blocked facts by blocker text (column 11). Run as ntbuild on the box.
usage: sample_cls.py [RESULTS_DIR] [--override PKG=RESULTS]..."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections, glob, os, sys
args = sys.argv[1:]
ov = {}
for i, a in enumerate(args):
    if a == '--override':
        k, v = args[i + 1].split('=', 1); ov[k] = v
pos = [a for i, a in enumerate(args) if not a.startswith('--') and (i == 0 or args[i - 1] != '--override')]
R = pos[0] if pos else (NT_BOX + '/results')
def c_of(v):
    verdict, reason, bl = v[5], v[6], (v[10] if len(v) > 10 else '')
    if verdict in ('ERROR', 'TIMEOUT'):
        return 'resources'
    if reason == 'blocked':
        if 'idOpaque' in bl or 'extrinsicFix' in bl: return 'iterator strings'
        if 'Lean.' in bl or 'PersistentHashMap' in bl: return 'meta layer'
        if 'getNumBits' in bl or 'hash' in bl.lower(): return 'HashMap/USize'
        if 'Float' in bl: return 'Float'
        if 'WellFounded.fix' in bl: return 'WF copies not bridged'
        return 'other blocked'
    return verdict + ':' + reason
cls = collections.Counter(); bypkg = collections.defaultdict(collections.Counter); sub = collections.Counter()
for f in sorted(glob.glob(os.path.join(R, 's_*.ax.tsv'))):
    p = os.path.basename(f)[2:-7]
    if p in ov:
        f = os.path.join(R, ov[p] + '.ax.tsv')
    last = {}
    for l in open(f, errors='ignore'):
        c = l.rstrip('\n').split('\t')
        if len(c) >= 7:
            last[(c[1], c[2])] = c
    for v in last.values():
        if v[5] in ('PROVED', 'NOT_BUILT'):
            continue
        k = c_of(v); cls[k] += 1; bypkg[k][p] += 1
        if k == 'resources': sub[v[5] + ':' + v[6]] += 1
print('failures', sum(cls.values()))
for k, n in cls.most_common():
    print(n, k, dict(bypkg[k].most_common(4)))
print('resources by reason', dict(sub))
