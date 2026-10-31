#!/usr/bin/env python3
"""v3b_export_v1.py (v3 BerryEsseen, parse-once covers; adapted from the archived export_axtsv.py): per-fact results of
the parse-once covers in the driver's .ax.tsv layout, from $NT_BOX/v3/berry/covers. One row per cover whose
modules have run: name v3b-covers-berry-esseen, module, axiom (from the check F2_<tag>; '-' if it has not run),
tactic, inner, verdict (PROVED when F2_<tag> reports PROVED through `NT kernel_fact`, else FAILED or NOT_RUN), reason
(kernel_fact, or the first module that did not finish), kernel_ms (sum of the kernel times of the tree, parse, leaf and
assembly declarations), maxrss_kb (largest peak of the cover's lean processes), secs (sum of their elapsed seconds; each
is single-threaded), blockers (empty), trace (final theorem, leaves, axioms of the final theorem).
usage: python3 -I v3b_export_v1.py OUT_TSV
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import glob, os, re, sys

C = (NT_BOX + '/v3/berry/covers')
out_path = sys.argv[1]
assert out_path.startswith((NT_BOX + '/v3/berry/results/')), out_path
rows = []
for d in sorted(glob.glob(f'{C}/*')):
    if not os.path.isdir(d):
        continue
    tag = os.path.basename(d)
    tree = open(f'{d}/BO_{tag}_Tree.lean').read()
    mod = re.search(r'^import (BerryEsseen\.Upper0423\.\S+)$', tree, re.M).group(1)
    def rd(p):
        return open(p, errors='replace').read() if os.path.exists(p) else ''
    def done(m):
        t = rd(f'{d}/{m}.log').splitlines()
        return os.path.exists(f'{d}/{m}.olean') and len(t) >= 2 and t[-2] == 'rc=0'
    mods = [f'BO_{tag}_Tree', f'BO_{tag}_Parse'] + [l.strip() for l in rd(f'{d}/batches.txt').splitlines() if l.strip()] + [f'BO_{tag}_All']
    f2, f2e = rd(f'{d}/F2_{tag}.log'), rd(f'{d}/F2_{tag}.err')
    m = re.search(r'PROVED `([^`]+)` as `([^`]+)`', f2)
    if m and 'NT kernel_fact' in f2e and re.search(r'^rc=0$', f2, re.M):
        verdict, reason, ax = 'PROVED', 'kernel_fact', m.group(1)
    else:
        first = next((x for x in mods if not done(x)), None)
        started = any(os.path.exists(f'{d}/{x}.log') for x in mods)
        verdict = 'FAILED' if started else 'NOT_RUN'
        reason = f'not done: {first}' if first else ('check F2 not PROVED' if f2 else 'check F2 not run')
        mf = re.search(r'FAILED `([^`]+)`', f2)
        ax = mf.group(1) if mf else '-'
    kms = 0
    for e in glob.glob(f'{d}/BO_{tag}_*.err'):
        t = rd(e)
        kms += sum(int(x) for x in re.findall(r'^BO leaf \S+ k=\d+ node=\d+ kernel_ms=(\d+)', t, re.M))
        kms += sum(int(x) for x in re.findall(r'^BO parse \S+ (?:hpL|parse) kernel_ms=(\d+)', t, re.M))
        kms += sum(int(a) + int(b) for a, b in re.findall(r'node_kernel_ms=(\d+) final_ms=(\d+)', t))
    secs, rss = 0.0, 0
    for tf in glob.glob(f'{d}/*.time'):
        mm = re.search(r'TIME ([\d.]+) s (\d+) KB', rd(tf))
        if mm:
            secs += float(mm.group(1)); rss = max(rss, int(mm.group(2)))
    nodes = re.search(r'nodes=(\d+)', rd(f'{d}/BO_{tag}_Tree.err'))
    leaves = (int(nodes.group(1)) + 1) // 2 if nodes else ''
    axl = re.search(r"depends on axioms: \[([^\]]*)\]", rd(f'{d}/BO_{tag}_All.log'))
    trace = f'BerryOpt.{tag}.final leaves={leaves} axioms=[{axl.group(1) if axl else "?"}]'
    rows.append('\t'.join(['v3b-covers-berry-esseen', mod, ax, 'native_decide', 'False', verdict, reason,
                           str(kms), str(rss), f'{secs:.0f}', '', trace]))
os.makedirs(os.path.dirname(out_path), exist_ok=True)
with open(out_path, 'w') as f:
    f.write('\n'.join(rows) + '\n')
print(len(rows), 'rows ->', out_path, '; PROVED', sum(1 for r in rows if '\tPROVED\t' in r))
