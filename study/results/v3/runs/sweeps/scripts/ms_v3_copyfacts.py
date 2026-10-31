#!/usr/bin/env python3
"""ms_v3_copyfacts.py: per converted fact with well-founded copies (v3 default run, corpus), whether its copied
definitions are core only, Mathlib only, the project's own only, or a mix (classes from agg/v2/modof2_<p>.tsv; the 2
_ktr.* names, copies that NativeTrust made of Strata's own definitions in an earlier phase, count as project).
Run on the box as ntbuild with python3 -I; prints counts per package and in total."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections, re
from pathlib import Path

H = Path(NT_BOX); A = H / 'v3' / 'sweeps' / 'agg' / 'v2'
PKGS = ['strata', 'cvc5-logos', 'cedar-lean', 'formal-conjectures', 'berry-esseen', 'humanfia-icho2026', 'asi-stack-book']
PROVED_RE = re.compile(r'^PROVED `([^`]+)`', re.M)
COPIES_RE = re.compile(r'^NT \S+ blockers_ms=\d+ bounded=\w+ copy_ms=\d+ copies=(\d+)', re.M)
COPY_RE = re.compile(r'^NT copy (\S+) defn_ms=', re.M)
tot = collections.Counter()
for p in PKGS:
    cls = {}
    for l in (A / f'modof2_{p}.tsv').read_text().splitlines():
        n, m, c = l.split('\t')
        cls[n] = {'library': 'Mathlib', 'unknown': 'project'}.get(c, c)
    facts = {}
    for run in (f'v3-{p}', f'v3r-{p}'):
        w = H / 'work' / run
        if w.is_dir():
            for lg in w.glob('ax[12]*_*.log'):
                t = lg.read_text(errors='ignore')
                m = PROVED_RE.search(t)
                if m:
                    facts[m.group(1)] = set(COPY_RE.findall(t)) if sum(int(x) for x in COPIES_RE.findall(t)) > 0 else None
    cnt = collections.Counter()
    for a, ns in facts.items():
        if ns:
            kinds = sorted({cls.get(n, '?') for n in ns})
            cnt['+'.join(kinds)] += 1
    tot.update(cnt)
    print(p, dict(cnt))
print('TOTAL', dict(tot))
