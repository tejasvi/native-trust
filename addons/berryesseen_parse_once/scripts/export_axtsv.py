#!/usr/bin/env python3
"""Per-fact results of BerryOpt in the driver's .ax.tsv layout (run as ntbuild: python3 -I export_axtsv.py).
Writes work_parse_once/results/berry-esseen-covers.ax.tsv with one row per converted fact:
name, module, axiom, tactic, inner, verdict (PROVED), reason (kernel_fact), kernel_ms (sum of the kernel times of the
tree/parse/leaf/assembly declarations), maxrss_kb (largest peak RSS of the fact's lean processes), secs (CPU-s: sum of
elapsed seconds of its single-threaded lean processes), blockers (empty), trace (final theorem, leaves, axioms).
Only facts whose driver-style check F2_<tag> reports `PROVED ... ` through `NT kernel_fact` are listed."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import glob, os, re
W = (NT_BOX + '/work_parse_once')
out = []
for d in sorted(glob.glob(f'{W}/covers/*')):
    if not os.path.isdir(d):
        continue
    tag = os.path.basename(d)
    f2, f2e = f'{d}/F2_{tag}.log', f'{d}/F2_{tag}.err'
    if not (os.path.exists(f2) and os.path.exists(f2e)):
        continue
    t2, t2e = open(f2).read(), open(f2e).read()
    m = re.search(r'PROVED `([^`]+)` as `([^`]+)`', t2)
    if not m or 'NT kernel_fact' not in t2e:
        continue
    ax = m.group(1)
    tree = open(f'{d}/BO_{tag}_Tree.lean').read()
    mod = re.search(r'^import (BerryEsseen\.Upper0423\.\S+)$', tree, re.M).group(1)
    kms = 0
    for e in glob.glob(f'{d}/BO_{tag}_*.err'):
        t = open(e).read()
        kms += sum(int(x) for x in re.findall(r'^BO leaf \S+ k=\d+ node=\d+ kernel_ms=(\d+)', t, re.M))
        kms += sum(int(x) for x in re.findall(r'^BO parse \S+ (?:hpL|parse) kernel_ms=(\d+)', t, re.M))
        kms += sum(int(a) + int(b) for a, b in re.findall(r'node_kernel_ms=(\d+) final_ms=(\d+)', t))
    secs, rss = 0.0, 0
    for tf in glob.glob(f'{d}/*.time'):
        mm = re.search(r'TIME ([\d.]+) s (\d+) KB', open(tf).read())
        if mm:
            secs += float(mm.group(1)); rss = max(rss, int(mm.group(2)))
    nodes = re.search(r'nodes=(\d+)', open(f'{d}/BO_{tag}_Tree.err').read())
    leaves = (int(nodes.group(1)) + 1) // 2 if nodes else ''
    axl = re.search(r"depends on axioms: \[([^\]]*)\]", open(f'{d}/BO_{tag}_All.log').read())
    trace = f'BerryOpt.{tag}.final leaves={leaves} axioms=[{axl.group(1) if axl else "?"}]'
    out.append('\t'.join(['berry-esseen-covers', mod, ax, 'native_decide', 'False', 'PROVED', 'kernel_fact',
                          str(kms), str(rss), f'{secs:.0f}', '', trace]))
with open(f'{W}/results/berry-esseen-covers.ax.tsv', 'w') as f:
    f.write('\n'.join(out) + '\n')
print(len(out), 'rows ->', f'{W}/results/berry-esseen-covers.ax.tsv')
