#!/usr/bin/env python3
"""List the proved facts of a run whose evaluation made >= 1 kernel-reducible copy (per-fact logs of m2_axioms*.py).
usage: wf_facts.py WORK_DIR  -> one axiom name per line on stdout; counts on stderr"""
import re, sys
from pathlib import Path
w = Path(sys.argv[1]); n = 0; out = set()
for lg in w.glob('ax[12]*_*.log'):
    t = lg.read_text(errors='ignore')
    m = re.search(r'^PROVED `([^`]+)`', t, re.M)
    if not m:
        continue
    n += 1
    if sum(int(x) for x in re.findall(r'^NT \S+ blockers_ms=\d+ bounded=\w+ copy_ms=\d+ copies=(\d+)', t, re.M)) > 0:
        out.add(m.group(1))
print('\n'.join(sorted(out)))
print(f"proved logs={n} with copies={len(out)}", file=sys.stderr)
