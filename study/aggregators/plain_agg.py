#!/usr/bin/env python3
"""Ablation summary (run as ntbuild on the box): for each package, compare the proved facts of the study run with
the same facts re-run with every transformation off (`wf := false, split := 1`, results NAME-plain). A fact that
is proved in the study run but not in the plain run needed a transformation. Inner facts are counted separately.
usage: plain_agg.py [RESULTS_DIR]"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections, os, sys
R = sys.argv[1] if len(sys.argv) > 1 else (NT_BOX + '/results')
PK = [('trainverify', 'trainverify'), ('cvc5-logos', 'cvc5-logos-fuel'), ('humanfia-icho2026', 'humanfia-icho2026'),
      ('formal-conjectures', 'formal-conjectures-fuel'), ('longfellow-zk', 'longfellow-zk'), ('asi-stack-book', 'asi-stack-book'),
      ('strata', 'strata-fuel'), ('sounio', 'sounio'), ('lido-srv3', 'lido-srv3'), ('cedar-lean', 'cedar-lean'),
      ('rs-mca-m31_dyadic_weight_laws', 'rs-mca-m31_dyadic_weight_laws'), ('rs-mca-m31_flatness_keystone', 'rs-mca-m31_flatness_keystone'),
      ('berry-esseen', 'berry-esseen'), ('clean', 'clean')]


def load(name):
    f = os.path.join(R, f"{name}.ax.tsv")
    last = {}
    if os.path.exists(f):
        for l in open(f, errors='ignore'):
            c = l.rstrip('\n').split('\t')
            if len(c) >= 7:
                last[(c[1], c[2])] = c
    return last


tot = collections.Counter()
print("package\tproved(study)\tre-run\tproved(plain)\tnot proved(plain): reasons")
for pkg, src in PK:
    a = {k: v for k, v in load(src).items() if v[5] == 'PROVED' and v[4] != 'True'}
    b = load(pkg + '-plain')
    rer = {k: v for k, v in b.items() if k in a}
    ok = sum(1 for v in rer.values() if v[5] == 'PROVED')
    bad = collections.Counter((v[5], v[6]) for v in rer.values() if v[5] != 'PROVED')
    tot['study'] += len(a); tot['rerun'] += len(rer); tot['plain'] += ok
    print(f"{pkg}\t{len(a)}\t{len(rer)}\t{ok}\t" + ' '.join(f"{x}/{y}={n}" for (x, y), n in bad.most_common()))
print(f"TOTAL\t{tot['study']}\t{tot['rerun']}\t{tot['plain']}\tneed a transformation (of re-run): {tot['rerun'] - tot['plain']}")
