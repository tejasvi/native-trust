#!/usr/bin/env python3
"""task 3: the driver's per-fact modules for one QEC theorem (read-only). The theorem's native axioms come from the
`#print axioms` output of the project's theorem files (lean4/logs/*.txt); each axiom's (module, index) from the driver's
listing logs; its fact module is F2_<suffix>_<module>_<index> of the run that PROVED it (heavy pass before pass 1), and
its .olean must exist. Prints a status line; writes the module names, one per line, to OUT only when every fact has
one. usage: fm_for_v1.py THEOREM OUT"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import re, sys
from pathlib import Path

Q = Path((NT_BOX + '/work_resv8/qec')); W = Q / 'drv' / 'qec'; M = W / 'mods'; R = Q / 'results'
SUF = '._native.native_decide.ax_1_1'
thm, outp = sys.argv[1], Path(sys.argv[2])
nat = None
for lg in sorted((Q / 'lean4' / 'logs').glob('*.txt')):
    for m in re.finditer(r"'([^']+)' depends on axioms: \[(.*?)\]", lg.read_text(errors='ignore'), re.S):
        if m.group(1) == thm:
            nat = sorted({x.strip() for x in m.group(2).split(',') if x.strip().endswith(SUF)})
if nat is None:
    sys.exit(f'{thm}: no #print axioms output found')
where = {}
for lg in W.glob('listax_*.log'):
    mod = lg.name[len('listax_'):-len('.log')]
    for l in lg.read_text(errors='ignore').splitlines():
        c = l.split('\t')
        if c[0] == 'AX' and len(c) >= 5:
            where[c[1]] = (mod, int(c[4]))
proved = {}
for suf, f in (('_p1', R / 'qec_p1.ax.tsv'), ('_heavy', R / 'qec_heavy.ax.tsv')):
    if f.exists():
        for l in f.read_text(errors='ignore').splitlines():
            c = l.split('\t')
            if len(c) >= 6 and c[5] == 'PROVED':
                proved[c[2]] = suf      # heavy rows come later and win
mods, miss = [], []
for a in nat:
    if a not in where or a not in proved:
        miss.append(a); continue
    mod, i = where[a]
    name = f"F2{proved[a]}_" + re.sub(r'[^A-Za-z0-9_]', '_', f"{mod}_{i}")[:150]
    if not (M / f"{name}.olean").exists():
        miss.append(a + ' (no olean ' + name + ')'); continue
    mods.append(name)
print(f"{thm}: native facts {len(nat)}, with a proved fact module {len(mods)}, missing {len(miss)}")
for x in miss[:20]:
    print('  MISSING', x)
if not miss:
    outp.write_text('\n'.join(mods) + '\n')
    print(f"wrote {outp}")
