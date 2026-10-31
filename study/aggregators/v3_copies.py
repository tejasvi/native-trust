#!/usr/bin/env python3
"""v3_copies.py: the well-founded copies of the final run's conversions (Section 4.6), from the shipped check logs of the
D passes (study/results/v3/logs/v3-<package>/, v3r-<package>/ and v3h-<package>/ of the corpus) and the module of each
copied definition (study/results/v3/runs/sweeps/agg/v2/modof2_<package>.tsv: definition, module, and core, library
(Mathlib), project or unknown). A conversion made copies when its log has a PROVED line and the copies fields of its NT
lines sum to more than 0, the rule of runs/sweeps/scripts/ms_v3_wf.py (the PROVED line alone reports the copies of the last
attempt only). The per-theorem driver's logs (rs-mca on Lean 4.28) have no NT lines; its one conversion that evaluates
well-founded recursion is counted from its check without the replacement (runs/wf_off/pte_wfoff_v1.log: the kernel stops at
WellFounded.fix through the definitions listed there, which the conversion therefore copies). Prints, per corpus package, the
facts with copies and those among them that copy a definition of core or Mathlib; then the distinct copied definitions of core
and of Mathlib, a comparison with the sweeps' list of them (runs/sweeps/agg/v2/core_lib_names.txt), and the origin of the
definitions named in the paper.
usage (from the artifact's top directory): python3 -I -B study/aggregators/v3_copies.py
"""
import collections
import glob
import gzip
import re

V3 = 'study/results/v3/'
origin = {}
for f in sorted(glob.glob(V3 + 'runs/sweeps/agg/v2/modof2_*.tsv')):
    for line in open(f, encoding='utf-8'):
        c = line.rstrip('\n').split('\t')
        if len(c) >= 3:
            origin.setdefault(c[0], c[2])
NT_COPIES = re.compile(r'^NT \S+ blockers_ms=\d+ bounded=\w+ copy_ms=\d+ copies=(\d+)', re.M)
facts, ext, names = collections.Counter(), collections.Counter(), collections.defaultdict(set)
for f in sorted(glob.glob(V3 + 'logs/v3*-*/ax*.log.gz')):
    run = f.split('/')[-2]
    pas, _, pkg = run.partition('-')
    if pas not in ('v3', 'v3r', 'v3h') or pkg.startswith('s_'):
        continue
    text = gzip.open(f, 'rt', encoding='utf-8', errors='replace').read()
    if not re.search(r'^PROVED `', text, re.M) or sum(int(x) for x in NT_COPIES.findall(text)) == 0:
        continue
    facts[pkg] += 1
    out = {n for n in re.findall(r'^NT copy (\S+) defn_ms=', text, re.M) if origin.get(n) in ('core', 'library')}
    if out:
        ext[pkg] += 1
        for n in out:
            names[origin[n]].add(n)
wf = open(V3 + 'runs/wf_off/pte_wfoff_v1.log', encoding='utf-8').read()
chain = re.search(r'via (\S+(?: → \S+)*) → WellFounded\.fix', wf)
if 'REJECTED' in wf and chain:
    facts['rs-mca-moment_to_max'] += 1
    out = {n for n in chain.group(1).split(' → ') if origin.get(n) in ('core', 'library')}
    if out:
        ext['rs-mca-moment_to_max'] += 1
        for n in out:
            names[origin[n]].add(n)
for pkg in sorted(facts):
    print(f'{pkg}\tfacts with copies {facts[pkg]}\tcopying core or Mathlib {ext[pkg]}')
print(f'TOTAL\tfacts with copies {sum(facts.values())}\tcopying core or Mathlib {sum(ext.values())}')
print(f"distinct copied definitions of core or Mathlib: core {len(names['core'])}, library {len(names['library'])}")
listed = set(open(V3 + 'runs/sweeps/agg/v2/core_lib_names.txt', encoding='utf-8').read().split())
copied = names['core'] | names['library']
print(f'core_lib_names.txt: {len(listed)} names; ' + ('the same set' if listed == copied else
      f'differs: only listed {sorted(listed - copied)}, only copied {sorted(copied - listed)}'))
for name in ('String.splitOn', 'String.trim', 'String.trimAscii', 'List.merge', 'List.mergeSort', 'Array.qsort'):
    print(f'{name}: ' + (origin[name] if name in copied else 'not copied'))
