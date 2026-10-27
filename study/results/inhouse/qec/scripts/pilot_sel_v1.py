#!/usr/bin/env python3
"""task 3: pick the pilot facts (one per check family, smallest instance) from the driver's listing logs
(WORK/qec/listax_<module>.log, lines AX<TAB>axiom<TAB>tactic<TAB>inner<TAB>index) and write an anchored --include
regex. Also prints the listing totals (modules listed, rc=0 listings, facts, inner facts). usage: pilot_sel_v1.py OUT_RE"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import re, sys
from pathlib import Path
W = Path((NT_BOX + '/work_resv8/qec/drv/qec'))
PILOT = ['QEC.ChecksN.N_X_3', 'QEC.Criterion.TypeCheck', 'QEC.ChecksN8.H8_0', 'QEC.ChecksN8.C8_0_3', 'QEC.ChecksN8.HS8',
         'QEC.ChecksN8.Tab8', 'QEC.ChecksN8.W8', 'QEC.ChecksNS.S8.H_0', 'QEC.ChecksNS.S8.NM', 'QEC.ChecksNS.S8.W',
         'QEC.ChecksNS.TabP8', 'QEC.ChecksNW.CritL', 'QEC.ChecksNW.L.NM']
rows = {}
nlog = nok = 0
for lg in sorted(W.glob('listax_*.log')):
    m = lg.name[len('listax_'):-len('.log')]
    t = lg.read_text(errors='ignore')
    nlog += 1
    nok += bool(re.search(r'^rc=0 ', t, re.M))
    rows[m] = [l.split('\t') for l in t.splitlines() if l.startswith('AX\t')]
facts = sum(len(v) for v in rows.values())
inner = sum(1 for v in rows.values() for r in v if len(r) > 3 and r[3] == 'true')
print(f"listings {nlog} (rc=0: {nok}), modules with facts {sum(1 for v in rows.values() if v)}, facts {facts}, inner {inner}")
pick = []
for m in PILOT:
    r = rows.get(m, [])
    if not r:
        print(f"MISSING {m}"); continue
    print(f"{m}: {len(r)} fact(s); pilot {r[0][1]}")
    pick.append(r[0][1])
Path(sys.argv[1]).write_text('^(?:' + '|'.join(re.escape(a) for a in pick) + ')$\n')
print(f"regex with {len(pick)} axioms -> {sys.argv[1]}")
