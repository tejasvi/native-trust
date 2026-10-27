#!/usr/bin/env python3
"""Pick 10 blocked BerryEsseen facts (seeded) and print module, axiom, index, statement line."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import random, re
from pathlib import Path
H = Path(NT_BOX)
last = {}
for l in (H / 'results/berry-esseen.ax.tsv').read_text(errors='ignore').splitlines():
    c = l.split('\t')
    if len(c) >= 11:
        last[(c[1], c[2])] = c
blocked = sorted(k for k, c in last.items() if c[5] == 'FAILED' and c[6] == 'blocked')
random.seed(20261023)
pick = random.sample(blocked, 10)
for m, ax in pick:
    idx = None
    for l in (H / 'work/berry-esseen' / f'listax_{m}.log').read_text(errors='ignore').splitlines():
        c = l.split('\t')
        if c[0] == 'AX' and c[1] == ax:
            idx = int(c[4])
    src = H / 'repos/berry-esseen' / (m.replace('.', '/') + '.lean')
    st = [l for l in src.read_text().splitlines() if l.startswith('theorem')]
    print('\t'.join([m, str(idx), ax, ' | '.join(st)[:300]]))
