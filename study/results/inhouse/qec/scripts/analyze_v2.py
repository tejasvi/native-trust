#!/usr/bin/env python3
"""task 3: per-theorem and per-family tables of the QEC NativeTrust run (read-only). v2 (from analyze_v1.py, not
used for results): an ERROR whose job was OOM-killed (trace `cg_oom_kill=1`) is `memory` whatever the classifier said
(the driver's classify() reports `deep_recursion` when a non-fatal "copy-rejected ... deep recursion" note is in the
log); facts of the four heavy families (heads, headsS, cover, heads8_size) that pass 1 did not run are counted as
`resource_sampled` (resource failures at the study limits, judged on the sampled facts); static blockers per fact
from `#kernel_blockers` (blockers/Blk_*.log); the uncapped runs (qec_unc) with their per-piece kernel times.

Inputs (box): RESULTS/qec_p1.ax.tsv (pass 1, 900 s / 48 GiB), RESULTS/qec_heavy.ax.tsv (3,600 s / 96 GiB, on pass-1
resource failures), RESULTS/qec_unc.ax.tsv (heads8_0, cover8_0_3 without the study limits, up to 4 h / 96 GiB); the
theorems' native axioms from the `#print axioms` output of the project's theorem files (lean4/logs/*.txt); the
listing (qec/all_axioms.txt). A fact's verdict is its heavy-pass verdict when it has one, else its pass-1 verdict;
its CPU is the sum of its jobs' cgroup CPU (trace `cg_cpu_s=`). Facts shared by several theorems count in each
theorem; totals count each fact once. usage: analyze_v2.py OUTDIR
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import re, sys
from collections import Counter, defaultdict
from pathlib import Path

Q = Path((NT_BOX + '/work_resv8/qec'))
RES = Q / 'results'
SUF = '._native.native_decide.ax_1_1'
HEAVY = re.compile(r'^(heads|cover)')
out = Path(sys.argv[1]); out.mkdir(parents=True, exist_ok=True)


def rows(f):
    r = {}
    if f.exists():
        for l in f.read_text(errors='ignore').splitlines():
            c = l.split('\t')
            if len(c) >= 12 and c[2] not in ('-', ''):
                r[c[2]] = c          # the last row of an axiom wins
    return r


def cpu(c):
    m = re.search(r'cg_cpu_s=([0-9.]+)', c[11])
    return float(m.group(1)) if m else 0.0


def verdict(c):
    v, r = c[5], c[6]
    if v == 'ERROR' and re.search(r'cg_oom_kill=[1-9]', c[11]):
        r = 'memory'
    return v, r


def klass(v, r):
    return ('converted' if v == 'PROVED' else 'blocked' if (v == 'FAILED' and r == 'blocked')
            else 'resource' if (v == 'TIMEOUT' or (v == 'ERROR' and r == 'memory')) else 'other')


fam = lambda a: re.sub(r'(_\d+)+$', '', a[:-len(SUF)] if a.endswith(SUF) else a)
allax = [l.strip() for l in (Q / 'all_axioms.txt').read_text().splitlines() if l.strip()]
p1 = rows(RES / 'qec_p1.ax.tsv'); hv = rows(RES / 'qec_heavy.ax.tsv'); unc = rows(RES / 'qec_unc.ax.tsv')
# static blockers
static = {}
for lg in sorted((Q / 'blockers').glob('Blk_*.log')):
    cur = None
    for l in lg.read_text(errors='ignore').splitlines():
        m = re.match(r'^`([^`]+)`: (no blocker|blockers:)', l)
        if m:
            cur = m.group(1); static.setdefault(cur, set()); continue
        m = re.match(r'^• `([^`]+)`:', l)
        if m and cur:
            static[cur].add(m.group(1))
facts = {}
for a in allax:
    if a in p1:
        c = p1[a]; fin = hv.get(a, c); v, r = verdict(fin); cls = klass(v, r)
        facts[a] = dict(v1=verdict(c), v=v, r=r, cls=cls, heavy=a in hv, cpu=cpu(c) + (cpu(hv[a]) if a in hv else 0.0),
                        secs1=float(c[9] or 0), peak1=c[8], blockers=fin[10])
    else:
        facts[a] = dict(v1=('', ''), v='NOT_RUN', r='', cls='resource_sampled' if HEAVY.match(a) else 'not_run',
                        heavy=False, cpu=0.0, secs1=0.0, peak1='', blockers='')
    facts[a]['static'] = sorted(static.get(a, set()))
# theorems -> native axioms
thm = {}
for lg in sorted((Q / 'lean4' / 'logs').glob('*.txt')):
    t = lg.read_text(errors='ignore')
    for m in re.finditer(r"'([^']+)' depends on axioms: \[(.*?)\]", t, re.S):
        nat = sorted({x.strip() for x in m.group(2).split(',') if x.strip().endswith(SUF)})
        if nat:
            thm[m.group(1)] = (nat, lg.name)
CL = ('converted', 'blocked', 'resource', 'resource_sampled', 'other', 'not_run')
L = ['theorem\tsource_log\tnative_facts\t' + '\t'.join(CL) + '\tcpu_h_run\tstatic_blockers(facts)\tunconverted_families']
for name, (nat, lg) in sorted(thm.items()):
    k = Counter(facts[a]['cls'] if a in facts else 'not_run' for a in nat)
    sb = Counter(b for a in nat if a in facts for b in facts[a]['static'])
    uf = Counter(fam(a) for a in nat if a in facts and facts[a]['cls'] != 'converted')
    L.append(f"{name}\t{lg}\t{len(nat)}\t" + '\t'.join(str(k[c]) for c in CL) +
             f"\t{sum(facts[a]['cpu'] for a in nat if a in facts) / 3600:.3f}\t" +
             ';'.join(f"{b}({n})" for b, n in sb.most_common()) + '\t' + ';'.join(f"{f}({n})" for f, n in sorted(uf.items())))
(out / 'theorems.tsv').write_text('\n'.join(L) + '\n')
F = ['family\tfacts\t' + '\t'.join(CL) + '\theavy_rerun\tcpu_h\tmax_secs_p1\tmax_peak_kb_p1\tstatic_blockers']
byf = defaultdict(list)
for a, f in facts.items():
    byf[fam(a)].append(f)
for fm, fs in sorted(byf.items()):
    k = Counter(f['cls'] for f in fs); sb = Counter(b for f in fs for b in f['static'])
    pk = [int(f['peak1']) for f in fs if str(f['peak1']).isdigit()]
    F.append(f"{fm}\t{len(fs)}\t" + '\t'.join(str(k[c]) for c in CL) + f"\t{sum(f['heavy'] for f in fs)}\t"
             f"{sum(f['cpu'] for f in fs) / 3600:.3f}\t{max(f['secs1'] for f in fs):.0f}\t{max(pk) if pk else ''}\t" +
             ';'.join(f"{b}({n})" for b, n in sb.most_common()))
(out / 'families.tsv').write_text('\n'.join(F) + '\n')
U = ['axiom\tverdict\treason\tsecs\tmaxrss_kb\tcpu_s\tpieces_done(eval_ms)']
for a, c in sorted(unc.items()):
    lg = None
    for p in (Q / 'drv' / 'qec').glob('ax2_unc_*.log'):
        if f'NT start {a}' in p.read_text(errors='ignore')[:5000]:
            lg = p
    ev = re.findall(r'\.(p_\d+) eval_ms=(\d+)', lg.read_text(errors='ignore')) if lg else []
    U.append(f"{a}\t{c[5]}\t{c[6]}\t{c[9]}\t{c[8]}\t{cpu(c):.0f}\t" + ';'.join(f"{p}={ms}" for p, ms in ev))
(out / 'uncapped.tsv').write_text('\n'.join(U) + '\n')
k = Counter(f['cls'] for f in facts.values())
tot = (f"facts {len(facts)}: " + ', '.join(f"{c} {k[c]}" for c in CL) +
       f"; heavy re-runs {sum(f['heavy'] for f in facts.values())}; CPU of fact runs {sum(f['cpu'] for f in facts.values()) / 3600:.2f} h"
       f" (pass 1 {sum(cpu(c) for c in p1.values()) / 3600:.2f} h, heavy {sum(cpu(c) for c in hv.values()) / 3600:.2f} h,"
       f" uncapped {sum(cpu(c) for c in unc.values()) / 3600:.2f} h); theorems {len(thm)};"
       f" facts with static blockers {sum(1 for f in facts.values() if f['static'])}")
(out / 'totals.txt').write_text(tot + '\n')
print(tot); print('\n'.join(L)); print('\n'.join(F)); print('\n'.join(U))
