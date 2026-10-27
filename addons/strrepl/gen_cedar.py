#!/usr/bin/env python3
"""Generate the cedar test modules (run as ntbuild): the 16 blocked cedar-lean facts.
CT.lean : NativeTrust + StrRepl + CedarRepl, #kernel_blockers_nth + prove_native_axiom_nth for each.
CT0.lean: control without StrRepl/CedarRepl (blockers only)."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
from pathlib import Path
H = Path(NT_BOX); D = H / 'strrepl/v4.35.0/cedar'
last = {}
for l in (H / 'results/cedar-lean.ax.tsv').read_text(errors='ignore').splitlines():
    c = l.split('\t')
    if len(c) >= 11:
        last[(c[1], c[2])] = c
blocked = sorted(k for k, c in last.items() if c[5] == 'FAILED' and c[6] == 'blocked')
todo = []
for m, ax in blocked:
    for l in (H / 'work/cedar-lean' / f'listax_{m}.log').read_text(errors='ignore').splitlines():
        c = l.split('\t')
        if c[0] == 'AX' and c[1] == ax:
            todo.append((m, int(c[4]), ax))
mods = sorted({m for m, _, _ in todo})
hdr = 'set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
(D / 'CT.lean').write_text('import NativeTrust\nimport StrRepl\nimport CedarRepl\n' + ''.join(f'import {m}\n' for m in mods) + hdr +
    ''.join(f'#kernel_blockers_nth {m} {i}\n' for m, i, _ in todo) +
    ''.join(f'prove_native_axiom_nth {m} {i} (config := {{ split := 8 }})\n' for m, i, _ in todo))
(D / 'CT0.lean').write_text('import NativeTrust\n' + ''.join(f'import {m}\n' for m in mods) + hdr +
    ''.join(f'#kernel_blockers_nth {m} {i}\n' for m, i, _ in todo))
print(len(todo), mods)
