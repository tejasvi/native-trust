#!/usr/bin/env python3
"""v3_paper_numbers_v5.py (2026-10-30; v4 + the median peak memory is taken over the converted corpus facts, as the paper
states it; the value was the same over all facts).
v3_paper_numbers_v4.py (2026-10-30; v3 + the study's class rule: a FAILED blocked fact goes to its blocked class
whatever stopped the capped evaluation, and only TIMEOUT, ERROR and FAILED other with a resource message go to the
resource row (as paper_numbers.py); axioms that do not state an equation (counted in the sample) get their own
class; 'formal-conj.\\ ' spacing; gains per package in the report and in macro vgainlist).
v3_paper_numbers_v3.py (2026-10-29; v2 + OUT = - prints every output to stdout, each after a line '== NAME';
numbers_v3.tex holds only the macro lines, so that it equals the paper's block between its BEGIN/END markers).
v3_paper_numbers_v2.py (2026-10-29; v1 + the per-fact figures from facts_D.tsv of v3_numbers_v5.py: converted
facts' wall time, peak memory, facts per tactic, inner facts, evaluations that reduce to false).
v3_paper_numbers_v1.py (2026-10-29): the numbers and tables of paper v3 from one output folder of v3_numbers_v4.py
(per_package.tsv, facts_not_converted_D.tsv). Writes, into OUT (created, must not exist):
  numbers_v3.tex  \\newcommand macros used in the text;
  table1_v3.tex   rows of Table 1 (package, domain, facts, study, final library, rate);
  table2_v3.tex   rows of Table 2 (classes of the facts the final library leaves, corpus);
  tableext_v3.tex rows of the components table (final library, + general add-ons, + options, + package add-ons);
  report_v3.txt   all of the above in plain text, plus the sample's classes.
Columns: D = the final library at the study's protocol (with the heavy pass); G = + general add-ons; P = + propSplit;
O = + the other opt-in options (the paper's options column is O, which includes P); K = + package add-ons.
usage: v3_paper_numbers_v5.py AGG_OUT OUT|-
"""
import collections, statistics, sys
from pathlib import Path

if len(sys.argv) != 3:
    sys.exit(__doc__)
A = Path(sys.argv[1])
OUT = None if sys.argv[2] == '-' else Path(sys.argv[2])
if OUT is not None:
    if OUT.exists():
        sys.exit(f'{OUT} exists')
    if OUT.resolve() == A.resolve() or A.resolve() in OUT.resolve().parents:
        sys.exit('refusing: OUT inside the input folder')
OUTPUTS = {}

DISPLAY = {'trainverify': ('TrainVerify (distributed-training graphs)', 'software'),
           'cvc5-logos': ('cvc5/logos (checker for cvc5 proofs)', 'software'),
           'humanfia-icho2026': ('Humanfia IChO 2026 (AI-written)', 'chemistry'),
           'formal-conjectures': ('formal-conjectures', 'mathematics'),
           'longfellow-zk': ('longfellow-zk (Lean model)', 'software'), 'asi-stack-book': ('asi-stack-book', 'software'),
           'rs-mca': ('rs-mca (8 sub-projects)', 'mathematics'), 'sounio': ('sounio', 'software'),
           'lido-srv3': ('lido-srv3 proof closure', 'software'), 'berry-esseen': ('BerryEsseen', 'mathematics'),
           'strata': ('Strata', 'software'), 'clean': ('clean (zk circuits)', 'software'),
           'cedar-lean': ('cedar-spec', 'software'), 'aks': ('aks', 'mathematics'),
           'sorting-network-expanders': ('sorting-network', 'mathematics'), 'aeneas-lean': ('aeneas', 'software')}
SHORT = {'formal-conjectures': 'formal-conj.\\ ', 'humanfia-icho2026': 'Humanfia', 'cvc5-logos': 'cvc5/logos',
         'sorting-network-expanders': 'sorting-network', 'aeneas-lean': 'aeneas', 'cedar-lean': 'cedar-spec',
         'berry-esseen': 'BerryEsseen', 'trainverify': 'TrainVerify', 'strata': 'Strata', 'longfellow-zk': 'longfellow-zk'}


def n(x):
    return f"{x:,}"


def pct(a, b):
    if b == 0:
        return '-'
    r = 100 * a / b
    if a == b:
        return '100\\%'
    if a == 0:
        return '0\\%'
    s = f"{r:.1f}"
    if s == '100.0':
        s = f"{r:.2f}"
    return s + '\\%'


rows = [l.split('\t') for l in (A / 'per_package.tsv').read_text().splitlines()]
hdr = rows[0]
per = {r[0]: dict(zip(hdr[1:], (int(x) if x.lstrip('-').isdigit() else x for x in r[1:]))) for r in rows[1:]}
corpus = [p for p in per if not p.startswith('s_')]
sample = [p for p in per if p.startswith('s_') and per[p]['facts'] > 0]
COLS = ['D', 'G', 'P', 'O', 'K']
macros, rep = [], []


DESC = {'vtotfacts': 'corpus facts', 'vtotconv': 'corpus facts converted in the final run',
        'vtotrate': 'pooled rate, final run', 'vtotfail': 'corpus facts not converted in the final run',
        'vwoTVrate': 'pooled rate without the largest package', 'vwoToprate': 'pooled rate without the three largest',
        'vmedian': 'per-package median rate, final run', 'vmean': 'per-package mean rate, final run',
        'vstudyrate': 'pooled rate of the study, same facts', 'vnlo': 'packages converting less than half',
        'vhimin': 'lowest rate among the packages converting at least half',
        'vlomax': 'highest rate among the packages converting less than half',
        'vtraced': 'failures with a traced class (Table 2 rows other than resources)',
        'vuntraced': 'failures at time, memory or recursion-depth limits', 'vresfail': 'the same, Table 2 resource row',
        'vsamppkg': 'sample runs with facts', 'vsampfacts': 'sample facts', 'vsampconv': 'sample facts converted, final run',
        'vsamprate': 'sample pooled rate, final run', 'vsampmedian': 'sample per-package median, final run',
        'vsampmean': 'sample per-package mean, final run',
        'vsampstudyconv': 'sample facts converted in the study (Zag from retry-zag, as the paper reports the study)',
        'vsampregress': 'sample facts converted in the study, not in the final run',
        'vconvsecmed': 'converted corpus facts: median wall seconds including the import',
        'vconvsecpninety': 'converted corpus facts: 90th percentile wall seconds',
        'vrssmed': 'converted corpus facts: median peak memory per process, GiB (KiB / 2^20)'}


def mac(name, val, note=''):
    note = note or DESC.get(name, '')
    macros.append(f"\\newcommand{{\\{name}}}{{{val}}}" + (f"   % {note}" if note else ''))


def pooled(pkgs, col):
    a = sum(per[p][col] for p in pkgs); b = sum(per[p]['facts'] for p in pkgs)
    return a, b


def stats(pkgs, col):
    rates = [per[p][col] / per[p]['facts'] for p in pkgs if per[p]['facts']]
    return statistics.median(rates), statistics.mean(rates)


# --- corpus, final library (D)
big = sorted(corpus, key=lambda p: -per[p]['facts'])
a, b = pooled(corpus, 'D')
mac('vtotfacts', n(b)); mac('vtotconv', n(a)); mac('vtotrate', pct(a, b)); mac('vtotfail', n(b - a))
a1, b1 = pooled([p for p in corpus if p != big[0]], 'D')
mac('vwoTVconv', n(a1), f'without {big[0]}, of {b1:,}'); mac('vwoTVrate', pct(a1, b1))
a3, b3 = pooled([p for p in corpus if p not in big[:3]], 'D')
mac('vwoTopconv', n(a3), f"without {', '.join(big[:3])}, of {b3:,}"); mac('vwoToprate', pct(a3, b3))
md, mn = stats(corpus, 'D')
mac('vmedian', f"{100 * md:.1f}\\%"); mac('vmean', f"{100 * mn:.1f}\\%")
sa = sum(per[p]['study'] for p in corpus)
mac('vstudyconv', n(sa), 'the study, same facts'); mac('vstudyrate', pct(sa, b))
mac('vregress', n(sum(per[p]['regressions'] for p in corpus)), 'converted in the study, not by the final library')
mac('vgain', n(sum(per[p]['gains'] for p in corpus)), 'converted by the final library, not in the study')
def prose_name(p):
    return DISPLAY.get(p, (p, ''))[0].split(' (')[0]
gl = sorted(((per[p]['gains'], p) for p in corpus if per[p]['gains']), key=lambda t: (-t[0], prose_name(t[1])))
mac('vgainlist', ', '.join(f"{prose_name(p)} {g}" for g, p in gl), 'the gains per package')
rep.append('gains per package (corpus): ' + ', '.join(f"{p} {g}" for g, p in gl))
hi = [p for p in corpus if per[p]['D'] / per[p]['facts'] >= 0.5]
lo = [p for p in corpus if per[p]['D'] / per[p]['facts'] < 0.5]
mac('vnhi', str(len(hi)), 'packages converting at least half'); mac('vnlo', str(len(lo)))
if hi:
    mac('vhimin', pct(min(per[p]['D'] for p in hi if per[p]['D'] / per[p]['facts'] == min(per[q]['D'] / per[q]['facts'] for q in hi)),
                      min(per[p]['facts'] for p in hi if per[p]['D'] / per[p]['facts'] == min(per[q]['D'] / per[q]['facts'] for q in hi))))
if lo:
    worst_hi = max(lo, key=lambda p: per[p]['D'] / per[p]['facts'])
    mac('vlomax', pct(per[worst_hi]['D'], per[worst_hi]['facts']))
rep.append(f"corpus D: {a:,}/{b:,} {pct(a, b)}; without {big[0]} {a1:,}/{b1:,} {pct(a1, b1)}; without top 3 "
           f"{a3:,}/{b3:,} {pct(a3, b3)}; median {100 * md:.1f}% mean {100 * mn:.1f}%; study {sa:,} {pct(sa, b)}; "
           f">=50%: {len(hi)} packages, <50%: {len(lo)}")

# --- Table 1
t1 = []
for grp in (sorted(hi, key=lambda p: -per[p]['facts']), sorted(lo, key=lambda p: -per[p]['facts'])):
    for p in grp:
        name, dom = DISPLAY.get(p, (p, ''))
        t1.append(f"{name} & {dom} & {n(per[p]['facts'])} & {n(per[p]['study'])} & {n(per[p]['D'])} & "
                  f"{pct(per[p]['D'], per[p]['facts'])}\\\\")
    t1.append('\\midrule')
t1.append(f"total & & {n(b)} & {n(sa)} & {n(a)} & {pct(a, b)}\\\\\\bottomrule")
OUTPUTS['table1_v3.tex'] = '\n'.join(t1) + '\n'
rep.append('Table 1:\n' + '\n'.join(t1))


# --- Table 2 (corpus)
def paper_class(pkg, f):
    v, why, cl, tac, det = f['verdict'], f['reason'], f['class'], f['tactic'], f['detail']
    if why == 'false_in_logic':
        return 'false in the logic'
    if det == 'does not state an equation':
        return 'does not state an equation'
    if v in ('TIMEOUT', 'ERROR') or (v == 'FAILED' and why != 'blocked' and det in (
            'kernel deep recursion', 'maxRecDepth', 'stack overflow', 'kernel ran out of resources', 'out of memory',
            'deterministic timeout')):
        return 'time, memory or recursion-depth limit'
    if v == 'FAILED' and why == 'blocked':
        if tac == 'bv_decide':
            return 'the LRAT parser of bv_decide'
        if pkg == 'strata':
            return "Lean's metaprogramming layer, HashMap, USize"
        if 'iterators/String.Slice' in cl:
            return 'iterator-based string functions'
        if 'USize' in cl and 'hashing' in cl:
            return 'HashMap, USize'
        if 'C primitive (extern)' in cl or 'Float' in cl or 'USize' in cl:
            return 'C primitives and platform constants'
        if 'WellFounded.fix' in cl:
            return 'WellFounded.fix'
        return 'blocked: ' + cl
    return f"{v} {why}: {det}"


fl = (A / 'facts_not_converted_D.tsv').read_text().splitlines()
fh = fl[0].split('\t')
fnc = [dict(zip(fh, l.split('\t'))) for l in fl[1:]]
def pkg_of(base):
    return 'rs-mca' if base.startswith('rs-mca-') else base
cls = collections.defaultdict(collections.Counter)
scls = collections.defaultdict(collections.Counter)
for f in fnc:
    p = pkg_of(f['base'])
    (scls if p.startswith('s_') else cls)[paper_class(p, f)][p] += 1
t2, traced, total = [], 0, 0
for k, c in sorted(cls.items(), key=lambda kv: (kv[0] == 'time, memory or recursion-depth limit', -sum(kv[1].values()))):
    m = sum(c.values()); total += m
    if k != 'time, memory or recursion-depth limit':
        traced += m
    t2.append(f"{k} & {n(m)} & " + ', '.join(f"{SHORT.get(p, p)} {q}" if len(c) > 1 else SHORT.get(p, p)
                                         for p, q in c.most_common()) + '\\\\')
OUTPUTS['table2_v3.tex'] = '\n'.join(t2) + '\n'
mac('vtraced', n(traced)); mac('vuntraced', n(total - traced))
res = cls.get('time, memory or recursion-depth limit', collections.Counter())
mac('vresfail', n(sum(res.values())))
rep.append(f"Table 2 (corpus, {total:,} facts; traced {traced:,}, not traced {total - traced:,}):\n" + '\n'.join(t2))
rep.append('sample classes:\n' + '\n'.join(f"  {k}\t{sum(c.values())}\t" + ', '.join(f"{p} {q}" for p, q in c.most_common())
                                           for k, c in sorted(scls.items(), key=lambda kv: -sum(kv[1].values()))))

# --- the components table: D, G, O (with P), K
ext = []
def ext_row(label, pkgs, kind):
    cells = []
    for col in ('study', 'D', 'G', 'O', 'K'):
        if kind == 'pooled':
            x, y = pooled(pkgs, col)
            cells.append(pct(x, y))
        elif kind == 'top3':
            bg = sorted(pkgs, key=lambda p: -per[p]['facts'])
            x, y = pooled([p for p in pkgs if p not in bg[:3]], col)
            cells.append(pct(x, y))
        else:
            cells.append(f"{100 * stats(pkgs, col)[0]:.1f}\\%")
    ext.append(f"{label} & " + ' & '.join(cells) + '\\\\')
ext_row('corpus, pooled', corpus, 'pooled'); ext_row('corpus without the three largest', corpus, 'top3')
ext_row('corpus, per-package median', corpus, 'median')
if sample:
    ext_row('random sample, pooled', sample, 'pooled'); ext_row('random sample, per-package median', sample, 'median')
OUTPUTS['tableext_v3.tex'] = '\n'.join(ext) + '\n'
rep.append('components table (study, D, G, O, K):\n' + '\n'.join(ext))
for col in COLS:
    x, y = pooled(corpus, col); x3, y3 = pooled([p for p in corpus if p not in big[:3]], col)
    rep.append(f"  corpus {col}: {x:,}/{y:,} {pct(x, y)}; without top 3 {x3:,}/{y3:,} {pct(x3, y3)}")

# --- the random sample (each run one package, as sample_agg2.py)
if sample:
    sa_, sb_ = pooled(sample, 'D')
    smd, smn = stats(sample, 'D')
    own = [p for p in sample if 'tejasvi_smale6' in p]
    sbig = max(sample, key=lambda p: per[p]['facts'])
    x, y = pooled([p for p in sample if p != sbig], 'D')
    mac('vsamppkg', str(len(sample))); mac('vsampfacts', n(sb_)); mac('vsampconv', n(sa_))
    mac('vsamprate', pct(sa_, sb_)); mac('vsampmedian', f"{100 * smd:.1f}\\%"); mac('vsampmean', f"{100 * smn:.1f}\\%")
    mac('vsampwoBigrate', pct(x, y), f'without the largest, {sbig}')
    st = sum(per[p]['study'] for p in sample)
    mac('vsampstudyconv', n(st)); mac('vsampregress', n(sum(per[p]['regressions'] for p in sample)))
    rep.append(f"sample D: {len(sample)} packages with facts, {sa_:,}/{sb_:,} {pct(sa_, sb_)}; median {100 * smd:.1f}% "
               f"mean {100 * smn:.1f}%; largest {sbig} ({per[sbig]['facts']}); without it {x:,}/{y:,} {pct(x, y)}; "
               f"own packages: {', '.join(f'{p} {per[p][chr(68)]}/{per[p][chr(102) + chr(97) + chr(99) + chr(116) + chr(115)]}' for p in own)}; "
               f"study {st:,}")

# --- per-fact figures of the corpus (as the study's paper_numbers.py: converted facts' wall time incl. import,
# median and 90th percentile; peak memory per process over all facts; facts per tactic; inner facts; false)
fd = (A / 'facts_D.tsv').read_text().splitlines()
fdh = fd[0].split('\t')
allf = [dict(zip(fdh, l.split('\t'))) for l in fd[1:]]
cf = [f for f in allf if not f['base'].startswith('s_')]
secs = sorted(int(f['secs']) for f in cf if f['verdict'] == 'PROVED' and f['secs'].isdigit())
q = lambda s, x: s[min(len(s) - 1, int(x * len(s)))]
rss = sorted(int(f['maxrss_kb']) for f in cf if f['verdict'] == 'PROVED' and f['maxrss_kb'].isdigit())
if secs:
    mac('vconvsecmed', f"{statistics.median(secs):.0f}"); mac('vconvsecpninety', str(q(secs, 0.9)))
if rss:
    mac('vrssmed', f"{statistics.median(rss) / 1048576:.1f}")
tac = collections.Counter(f['tactic'] for f in cf)
inner = collections.Counter(f['verdict'] for f in cf if f['inner'] == 'True')
falses = sum(1 for f in allf if f['reason'] == 'false_in_logic')
mac('vperfact', n(len(cf)), 'facts of the per-fact driver (corpus)')
rep.append(f"corpus per-fact rows: {len(cf):,}; by tactic {dict(tac)}; inner facts {sum(inner.values())} {dict(inner)}; "
           f"converted fact secs median {statistics.median(secs) if secs else '-'} p90 {q(secs, 0.9) if secs else '-'}; "
           f"peak memory median {statistics.median(rss) / 1048576 if rss else 0:.2f} GiB; false_in_logic (all) {falses}")
OUTPUTS['numbers_v3.tex'] = '\n'.join(macros) + '\n'
OUTPUTS['report_v3.txt'] = '\n'.join(rep) + '\n'
if OUT is None:
    for name in ('numbers_v3.tex', 'table1_v3.tex', 'table2_v3.tex', 'tableext_v3.tex', 'report_v3.txt'):
        sys.stdout.write(f"== {name}\n{OUTPUTS[name]}")
else:
    OUT.mkdir(parents=True)
    for name, text in OUTPUTS.items():
        (OUT / name).write_text(text)
    print('\n'.join(rep))
