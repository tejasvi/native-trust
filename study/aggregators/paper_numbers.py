#!/usr/bin/env python3
"""The study's numbers as the paper reports them (Tables 1 and 2, Sections 4.1-4.3), from the result files.

usage: python3 -I study/aggregators/paper_numbers.py [RESULTS_M2_DIR]     (default study/results/m2)

Reads, under RESULTS_M2_DIR:
  ax/*.ax.tsv          per-fact results of the study run (the files m2_aggregate_ax.py aggregates; names ending in
                       -remedy or -fuel are experiments and are left out, as there);
  pertheorem/*.tsv     the six rs-mca sub-projects measured with the earlier per-theorem driver (m2_aggregate2.py);
  logs/<pkg>/*.log     per-fact logs, used only to leave out axioms that do not state an equation (as
                       m2_aggregate_ax.py does);
  facts_not_proved.tsv the class of every fact not converted (m2_aggregate_ax.py --tsv).
Counting rules are those of the aggregators: the last line per (package, module, axiom) counts; NOT_BUILT lines
are modules that did not build. The paper counts rs-mca's 8 sub-projects as one package, and groups the
aggregator's classes as in Table 2 (the mapping is the function paper_class below).
"""
import collections
import statistics
import sys
from pathlib import Path

D = Path(sys.argv[1] if len(sys.argv) > 1 else 'study/results/m2')
EXP = ('-remedy', '-fuel')
NAMES = {'trainverify': 'TrainVerify', 'cvc5-logos': 'cvc5/logos', 'humanfia-icho2026': 'Humanfia IChO 2026',
         'formal-conjectures': 'formal-conjectures', 'longfellow-zk': 'longfellow-zk',
         'asi-stack-book': 'asi-stack-book', 'rs-mca': 'rs-mca (8 sub-projects)', 'sounio': 'sounio',
         'lido-srv3': 'lido-srv3', 'berry-esseen': 'BerryEsseen', 'strata': 'Strata', 'clean': 'clean',
         'cedar-lean': 'cedar-spec', 'aks': 'aks', 'sorting-network-expanders': 'sorting-network',
         'aeneas-lean': 'aeneas'}


def pkg_of(name):
    return 'rs-mca' if name.startswith('rs-mca-') else name


# --- per-fact results
rows = {}
for f in sorted((D / 'ax').glob('*.ax.tsv')):
    for line in f.read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) < 6:
            continue
        c += [''] * (12 - len(c))
        rows[(c[0], c[1], c[2])] = c
have_mod = {(c[0], c[1]) for c in rows.values() if c[5] != 'NOT_BUILT'}
rows = [c for c in rows.values() if c[5] != 'NOT_BUILT' or (c[0], c[1]) not in have_mod]
rows = [c for c in rows if not c[0].endswith(EXP)]


def not_an_equation(c):
    if not (c[5] == 'FAILED' and c[6] == 'other'):
        return False
    for lg in (D / 'logs' / c[0]).glob('ax[12]_*.log'):
        t = lg.read_text(errors='ignore')
        if f"FAILED `{c[2]}`" in t and 'does not state an equation' in t:
            return True
    return False


excluded = [c for c in rows if not_an_equation(c)]
rows = [c for c in rows if c not in excluded]
facts = [c for c in rows if c[5] != 'NOT_BUILT']
notbuilt = [c for c in rows if c[5] == 'NOT_BUILT']

# --- per-theorem results (rs-mca)
pt = {}
for f in sorted((D / 'pertheorem').glob('*.tsv')):
    for line in f.read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) >= 4:
            pt[(c[0], c[1], c[2])] = c
pt = [c for c in pt.values() if c[3] != 'NOT_BUILT']

per = collections.defaultdict(lambda: [0, 0])
for c in facts:
    p = pkg_of(c[0])
    per[p][0] += 1
    per[p][1] += c[5] == 'PROVED'
for c in pt:
    p = pkg_of(c[0])
    per[p][0] += 1
    per[p][1] += c[3] == 'KERNELIZED'
nfacts = sum(v[0] for v in per.values())
nconv = sum(v[1] for v in per.values())
rate = {p: v[1] / v[0] for p, v in per.items()}
order = sorted(per, key=lambda p: (-(rate[p] >= 0.5), -per[p][0]))

print("Table 1 (native facts converted automatically, per package):")
print("package\tfacts\tconverted\trate")
for p in order:
    print(f"{NAMES.get(p, p)}\t{per[p][0]:,}\t{per[p][1]:,}\t{100 * rate[p]:.2f}%")
print(f"total\t{nfacts:,}\t{nconv:,}\t{100 * nconv / nfacts:.1f}%")
print(f"packages: {len(per)}; failures: {nfacts - nconv:,}")
hi = sorted(r for r in rate.values() if r >= 0.5)
lo = sorted(r for r in rate.values() if r < 0.5)
print(f"packages converting >= 50%: {len(hi)}, lowest rate among them {100 * hi[0]:.1f}%; "
      f"others: {len(lo)}, highest rate among them {100 * lo[-1]:.1f}%")
print(f"per-package rate: median {100 * statistics.median(rate.values()):.1f}%, "
      f"mean {100 * statistics.mean(rate.values()):.1f}%")
big = sorted(per, key=lambda p: -per[p][0])
tv = per['trainverify']
print(f"largest package: {NAMES[big[0]]} {tv[0]:,} facts = {100 * tv[0] / nfacts:.1f}% of all")
rest = [v for p, v in per.items() if p != 'trainverify']
a, b = sum(v[1] for v in rest), sum(v[0] for v in rest)
print(f"without {NAMES[big[0]]}: {a:,} of {b:,} = {100 * a / b:.1f}%")
rest3 = [v for p, v in per.items() if p not in big[:3]]
a, b = sum(v[1] for v in rest3), sum(v[0] for v in rest3)
print(f"without the three largest ({', '.join(NAMES[p] for p in big[:3])}): {a:,} of {b:,} = {100 * a / b:.1f}%")

print("\nper-fact driver:")
print(f"facts measured with the per-fact driver: {len(facts):,}; with the per-theorem driver: {len(pt)} "
      f"(sub-projects: {len({c[0] for c in pt})})")
tac = collections.Counter(c[3] for c in facts)
print("by tactic: " + ', '.join(f"{t} {n:,}" for t, n in tac.most_common()))
inner = collections.Counter(c[5] for c in facts if c[4] == 'True')
print(f"facts inside definitions or instances: {sum(inner.values())} ({dict(inner)})")
print(f"evaluations that reduced to false (false_in_logic): {sum(1 for c in facts if c[6] == 'false_in_logic')}")
secs = sorted(int(c[9]) for c in facts if c[5] == 'PROVED' and c[9].isdigit())
q = lambda s, x: s[min(len(s) - 1, int(x * len(s)))]
print(f"converted fact, wall time incl. import: median {statistics.median(secs):.0f} s, p90 {q(secs, 0.9)} s")
rss = sorted(int(c[8]) for c in facts if c[8].isdigit())
print(f"peak memory per process: median {statistics.median(rss) / 1048576:.1f} GiB (maxrss in KiB / 2^20)")
nb = collections.Counter(c[0] for c in notbuilt)
print(f"modules not built: {len(notbuilt)}: " + ', '.join(f"{p} {n}" for p, n in nb.most_common()))
print(f"left out (axioms that do not state an equation): {len(excluded)} "
      f"({', '.join(sorted({c[0] for c in excluded}))})")


# --- Table 2: classes of the facts not converted
def paper_class(pkg, verdict, reason, construct):
    if construct.startswith('iterators/String.Slice'):
        return 'iterator-based string functions'
    if pkg == 'strata' and verdict == 'FAILED' and reason == 'blocked':
        return "Lean's metaprogramming layer, HashMap, USize"
    if verdict == 'FAILED' and reason == 'other' and pkg in ('asi-stack-book', 'formal-conjectures'):
        return 'casts along propext/Quot.sound equalities in decidability instances'
    if verdict == 'FAILED' and reason == 'other' and pkg == 'longfellow-zk':
        return 'time, memory or recursion-depth limit'   # deep recursion (Nat.choose by unary recursion)
    if construct.startswith('kernel resources'):
        return 'time, memory or recursion-depth limit'
    if pkg == 'clean' and verdict == 'FAILED' and reason == 'blocked':
        return 'the LRAT parser of bv_decide'
    if verdict == 'FAILED' and reason == 'blocked':
        return 'C primitives and platform constants'
    return 'unmapped: ' + construct


fnp = (D / 'facts_not_proved.tsv').read_text().splitlines()[1:]
cls = collections.defaultdict(collections.Counter)
for line in fnp:
    pkg, mod, ax, verdict, reason, construct, bl = (line.split('\t') + [''] * 7)[:7]
    cls[paper_class(pkg, verdict, reason, construct)][NAMES.get(pkg_of(pkg), pkg)] += 1
for c in pt:
    if c[3] != 'KERNELIZED':
        cls['not classified (earlier driver version)'][NAMES['rs-mca']] += 1
print("\nTable 2 (facts not converted, by class):")
traced = 0
for k in ['iterator-based string functions', "Lean's metaprogramming layer, HashMap, USize",
          'casts along propext/Quot.sound equalities in decidability instances', 'C primitives and platform constants',
          'the LRAT parser of bv_decide', 'time, memory or recursion-depth limit',
          'not classified (earlier driver version)'] + sorted(k for k in cls if k.startswith('unmapped')):
    n = sum(cls[k].values())
    if k not in ('time, memory or recursion-depth limit', 'not classified (earlier driver version)'):
        traced += n
    print(f"{k}\t{n}\t" + ', '.join(f"{p} {m}" for p, m in cls[k].most_common()))
total = sum(sum(v.values()) for v in cls.values())
print(f"total {total:,}; traced (first five classes) {traced}; not traced {total - traced}")
