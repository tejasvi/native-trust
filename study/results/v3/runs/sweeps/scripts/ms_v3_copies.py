#!/usr/bin/env python3
"""ms_v3_copies.py: the definitions copied by well-founded replacement in the v3 default run (run on the box as
ntbuild, python3 -I). For each corpus package: the final per-fact logs (work/v3-<p>, then work/v3r-<p> laid over, by
axiom) that report PROVED with copies > 0; the copied constants are the names on their `NT copy <name> ...` lines.
Writes $NT_BOX/v3/sweeps/agg/v2/copies_<p>.tsv (constant, facts using it) and prints per-package counts."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections, re
from pathlib import Path

H = Path(NT_BOX)
PKGS = ['trainverify', 'strata', 'cvc5-logos', 'lido-srv3', 'cedar-lean', 'aks', 'sorting-network-expanders', 'aeneas-lean',
        'rs-mca-m31_dyadic_weight_laws', 'rs-mca-m31_flatness_keystone', 'formal-conjectures', 'longfellow-zk',
        'berry-esseen', 'humanfia-icho2026', 'sounio', 'asi-stack-book', 'clean']
PROVED_RE = re.compile(r'^PROVED `([^`]+)`', re.M)
COPIES_RE = re.compile(r'^NT \S+ blockers_ms=\d+ bounded=\w+ copy_ms=\d+ copies=(\d+)', re.M)
COPY_RE = re.compile(r'^NT copy (\S+) defn_ms=', re.M)
out = H / 'v3' / 'sweeps' / 'agg' / 'v2'
out.mkdir(parents=True, exist_ok=True)
for p in PKGS:
    facts = {}
    for run in (f'v3-{p}', f'v3r-{p}'):
        w = H / 'work' / run
        if w.is_dir():
            for lg in w.glob('ax[12]*_*.log'):
                t = lg.read_text(errors='ignore')
                m = PROVED_RE.search(t)
                if m:
                    facts[m.group(1)] = (sum(int(x) for x in COPIES_RE.findall(t)) > 0, set(COPY_RE.findall(t)))
    use = collections.Counter()
    for a, (c, names) in facts.items():
        if c:
            for n in names:
                use[n] += 1
    if use:
        (out / f'copies_{p}.tsv').write_text(''.join(f'{n}\t{k}\n' for n, k in sorted(use.items())))
        print(f'{p}\tfacts_with_copies={sum(1 for c, _ in facts.values() if c)}\tdistinct_copied={len(use)}')
