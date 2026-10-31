#!/usr/bin/env python3
"""ms_v3_heavyonly.py: converted corpus facts that the v3 ablation leaves out (run on the box as ntbuild, python3 -I):
(1) facts converted only in the heavy pass: PROVED (KERNELIZED for the per-theorem driver) in a v3h-<pkg>*.ax.tsv /
v3h-<pkg>*.tsv file while their last verdict in the default run (v3-<pkg>, v3r-<pkg> laid over) is not PROVED/KERNELIZED;
outer facts only (inner != True) for .ax.tsv files; (2) the rs-mca Lean 4.28 sub-projects' per-theorem results
(v3-rs-mca-*.tsv, m2_repo4.py), which the per-fact plain runs cannot re-run. Prints one line per package."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections
from pathlib import Path

R = Path((NT_BOX + '/results'))
CORPUS = ['trainverify', 'strata', 'cvc5-logos', 'lido-srv3', 'cedar-lean', 'aks', 'sorting-network-expanders', 'aeneas-lean',
          'rs-mca-m31_dyadic_weight_laws', 'rs-mca-m31_flatness_keystone', 'formal-conjectures', 'longfellow-zk',
          'berry-esseen', 'humanfia-icho2026', 'sounio', 'asi-stack-book', 'clean', 'rs-mca-RS_disproof_v3',
          'rs-mca-cs25_cap_v13', 'rs-mca-moment_to_max', 'rs-mca-razorband_witness', 'rs-mca-syndrome_line',
          'rs-mca-syndrome_secant']
OK = ('PROVED', 'KERNELIZED')


def last(f, per_theorem):
    out = {}
    for l in f.read_text(errors='ignore').splitlines():
        c = l.split('\t')
        if per_theorem and len(c) >= 4:
            out[(c[1], c[2])] = (c[3], 'False')
        elif not per_theorem and len(c) >= 7:
            out[(c[1], c[2])] = (c[5], c[4])
    return out


tot = collections.Counter()
for p in CORPUS:
    d = {}
    for name in (f'v3-{p}', f'v3r-{p}'):
        for ext, pt in (('.ax.tsv', False), ('.tsv', True)):
            f = R / f'{name}{ext}'
            if f.exists() and not (ext == '.tsv' and (R / f'{name}.ax.tsv').exists() and f.name.endswith('.ax.tsv')):
                if ext == '.tsv' and f.name.endswith('.ax.tsv'):
                    continue
                d.update(last(f, pt))
    conv_default = {k for k, (v, inn) in d.items() if v in OK and inn != 'True'}
    heavy = {}
    for f in sorted(R.glob(f'v3h-{p}*')):
        stem = f.name.split('.')[0]
        if stem != f'v3h-{p}' and not stem.startswith(f'v3h-{p}_'):
            continue
        pt = not f.name.endswith('.ax.tsv')
        for k, (v, inn) in last(f, pt).items():
            if v in OK and inn != 'True':
                heavy.setdefault(k, f.name)
    only = {k: fn for k, fn in heavy.items() if k not in conv_default}
    pertheorem = p.startswith('rs-mca-') and (R / f'v3-{p}.tsv').exists() and not (R / f'v3-{p}.ax.tsv').exists()
    tot['default'] += len(conv_default); tot['heavy_only'] += len(only)
    if pertheorem:
        tot['pertheorem'] += len(conv_default)
    if conv_default or only:
        print(f'{p}\tdefault_converted_outer={len(conv_default)}\theavy_only={len(only)}\tper_theorem={pertheorem}\t'
              + ' '.join(sorted(set(only.values()))))
print(f'TOTAL\tdefault_converted_outer={tot["default"]} (of them per-theorem {tot["pertheorem"]})\theavy_only={tot["heavy_only"]}')
