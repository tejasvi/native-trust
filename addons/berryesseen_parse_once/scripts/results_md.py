#!/usr/bin/env python3
"""Write work_parse_once/results/RESULTS_covers.md: one row per BerryOpt cover run (run as ntbuild: python3 -I results_md.py).
CPU-s = sum of the elapsed seconds of all its single-threaded lean processes (LEAN_NUM_THREADS=1, -j1): tree, parse,
leaf modules, assembly, final check; peak GB = largest maximum RSS among them."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import glob, os, re, statistics
W = (NT_BOX + '/work_parse_once')
mods = {}
for l in open(f'{W}/covers/queue4_all.txt') if os.path.exists(f'{W}/covers/queue4_all.txt') else []:
    pass
def tm(path):
    try:
        m = re.search(r'TIME ([\d.]+) s (\d+) KB', open(path).read())
        return (float(m.group(1)), int(m.group(2)) / 1048576) if m else None
    except OSError:
        return None
order = {}
for f in ('next_order.txt', 'next_order_dw_unused.txt'):
    p = f'{W}/covers/{f}'
    if os.path.exists(p):
        for l in open(p):
            c = l.rstrip('\n').split('\t')
            if len(c) >= 2:
                order[c[0]] = c[1]
for t, m in (('C3', 'Small.Data.Cover3'), ('C4', 'Small.Data.Cover4'), ('C5', 'Small.Data.Cover5'), ('C6', 'Small.Data.Cover6')):
    order[t] = m
rows = []
tot_cpu = 0.0; tot_leaves = 0; conv = 0
for d in sorted(glob.glob(f'{W}/covers/*')):
    if not os.path.isdir(d):
        continue
    tag = os.path.basename(d)
    if not os.path.exists(f'{d}/BO_{tag}_Tree.log'):
        continue
    times = [x for x in (tm(p) for p in glob.glob(f'{d}/*.time')) if x]
    cpu = sum(t for t, _ in times); peak = max((g for _, g in times), default=0)
    leaf_ms = []
    for e in glob.glob(f'{d}/BO_{tag}_L*.err'):
        leaf_ms += [int(x) for x in re.findall(r'^BO leaf \S+ k=\d+ node=\d+ kernel_ms=(\d+)', open(e).read(), re.M)]
    nleaves = len(open(f'{d}/batches.txt').read().split())
    pe = open(f'{d}/BO_{tag}_Parse.err').read() if os.path.exists(f'{d}/BO_{tag}_Parse.err') else ''
    pm = re.search(r'hpL kernel_ms=(\d+)', pe)
    pt = tm(f'{d}/BO_{tag}_Parse.time')
    tr = re.search(r'BO tree \S+ chars=(\d+) pieces=(\d+) tokens=(\d+) nodes=(\d+)', open(f'{d}/BO_{tag}_Tree.err').read()) if os.path.exists(f'{d}/BO_{tag}_Tree.err') else None
    al = open(f'{d}/BO_{tag}_All.log').read() if os.path.exists(f'{d}/BO_{tag}_All.log') else ''
    ax = re.search(r"'BerryOpt\.\S+\.final' depends on axioms: \[([^\]]*)\]", al)
    f2 = open(f'{d}/F2_{tag}.log').read() if os.path.exists(f'{d}/F2_{tag}.log') else ''
    f2e = open(f'{d}/F2_{tag}.err').read() if os.path.exists(f'{d}/F2_{tag}.err') else ''
    ok = bool(re.search(r'\bPROVED `', f2)) and 'NT kernel_fact' in f2e
    nl = int(tr.group(4)) if tr else 0
    leaves = (nl + 1) // 2 if nl else len(leaf_ms)
    s = sorted(leaf_ms)
    if ok:
        conv += 1; tot_leaves += leaves
    tot_cpu += cpu
    modname = order.get(tag, '')
    tf = f'{d}/BO_{tag}_Tree.lean'
    if os.path.exists(tf):
        mm = re.search(r'^import (BerryEsseen\.Upper0423\.\S+)$', open(tf).read(), re.M)
        if mm:
            modname = mm.group(1).replace('BerryEsseen.Upper0423.', '')
    rows.append((tag, modname, 'yes' if ok else ('running' if not f2 else 'no'), leaves, len(s),
                 f'{cpu:.0f}', f'{peak:.1f}', f'{int(pm.group(1))/1000:.1f}' if pm else '', f'{pt[1]:.1f}' if pt else '',
                 f'{statistics.median(s)/1000:.1f}' if s else '', f'{s[-1]/1000:.1f}' if s else '',
                 ax.group(1) if ax else '', tr.group(1) if tr else ''))
with open(f'{W}/results/RESULTS_covers.md', 'w') as f:
    f.write('| cover | module | converted | leaves | leaves done | CPU-s | peak GB | parse once s | parse GB | leaf median s | leaf max s | axioms of `BerryOpt.<tag>.final` | chars |\n')
    f.write('|---|---|---|---:|---:|---:|---:|---:|---:|---:|---:|---|---:|\n')
    for r in rows:
        f.write('| ' + ' | '.join(str(x) for x in r) + ' |\n')
    f.write(f'\nConverted: {conv} facts, {tot_leaves} leaves; CPU-s of all runs so far: {tot_cpu:.0f} ({tot_cpu/3600:.1f} CPU-h).\n')
print(open(f'{W}/results/RESULTS_covers.md').read())
