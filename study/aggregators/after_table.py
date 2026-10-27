#!/usr/bin/env python3
"""Facts converted per package, in the study and after the later work (Section "Closing the blocked classes").

usage: python3 -I -B study/aggregators/after_table.py [--tsv OUT.tsv] [--facts OUT.tsv] [--regressions OUT.tsv]
       (from the artifact's top directory)

Five cumulative columns for every package of the corpus (Table 1: 16 packages, 52,821 facts) and of the random
sample (26 packages with facts, 2,018 facts), with the study's denominators:
  study     the study's verdicts, counted as the paper counts them: study/results/m2 as paper_numbers.py (the last
            line per fact; modules that did not build, experiments and axioms that do not state an equation left
            out; rs-mca's per-theorem results), study/results/sample as sample_agg2.py with --no-default-overrides
            --override FrederickPu_Zag=retry-zag;
  library   + facts PROVED in later automatic runs of the library (versions v8 to v13, no add-ons);
  general   + the general add-ons: addons/bvs (all bv_decide facts) and the csimp add-on (Mathlib's own @[csimp]
            theorems as retry replacements, for any project that uses Mathlib);
  options   + library v13 with opt-in options, one fact per run: stage := true (staged evaluation), csimp := true
            (@[csimp] replacements in the kernel), propSplit := true with split := 16; no add-ons;
  specific  + the package-specific add-ons: BerryEsseen's tokenizer add-on, its parse-once covers, NTBobDeq (addons/bob)
            for BobDyLean, clean's four norm_num primality proofs of its own prime constants (@[kernel_fact],
            study/remedies/clean), and addons/longfellow, addons/fcprimes, addons/regex, addons/strata and addons/minidregg.
Each fact is credited to the most general mechanism that converts it: the columns are taken in the order above, so a
package-specific add-on gets only the facts that no library run, general add-on or opt-in option converts.
Only PROVED rows count, and only for facts of the study (a fact is matched by package, module and axiom name); a fact
counts once, in the first column whose sources prove it. PROVED rows for other axioms are reported, not counted.

Sources, under study/results/after/ unless noted:
  library/runs/<run>.ax.tsv   per-fact runs of library v8-v14 (same format as the study's .ax.tsv): v8r-<pkg> and
                              v8rp-<pkg> (re-runs of the facts that failed for resources at the study budget, the
                              second with propSplit), v9c-v14c (decidability instances built by casts), v8s-*-nt9c,
                              v11s-v14s (iterator-based string functions), v8-v14 (regression gates: every fact
                              PROVED in a baseline run, or a sample of it, re-run; zag-all re-runs all 23 Zag facts);
                              v14s-ninegates-all (all 14 ninegates facts with library v14's word-size case split, 3,600 s
                              per fact, 48 GiB address-space cap);
                              v13c-humanfia-icho2026 is, despite its prefix, the high-cap re-run of one Humanfia fact (library
                              v13, propSplit, 200 GiB address-space cap, 900 s) and counts with the high-cap re-runs;
  library/types/*.ax.tsv      copies in types (Zag, minidregg);
  library/shards/<tag>/       facts proved in pieces in separate modules: Comb_<tag>.log (the combining module's
                              PROVED line), cmd.txt (module and index of the fact);
  library/highcap/C_final.tsv  re-runs of the 48 facts with a single piece above 48 GiB (library v13, split := 8, propSplit := true,
                              up to 3,600 s; a 200 GiB cap on the address space in rounds w1-w3 and on memory, by systemd
                              MemoryMax, in round w4; one row per fact, the latest finished round; peak_kb = maximal resident
                              memory; as96_*: the same fact re-run under a hard 96 GiB address-space cap, for the facts near
                              that line): a fact PROVED within 3,600 s that fits the heavy pass's limits (the 96 GiB re-run
                              PROVED where there is one, otherwise a peak of at most 96 GiB) counts under library; one that needed
                              more is reported on its own line and counted in no column;
  library/shard_conversions.tsv  an earlier pass over the facts that failed for resources (one line per fact; no
                              header; column 10 verdict, column 14 technique): only its rows with technique
                              "shards" are used (16 longfellow facts; the later re-runs reproduce its other rows);
  study/results/bv_decide/    sweep/final_per_fact.tsv and final9.tsv (bvd_213.py checks them);
  study/results/m2/ax/clean-remedy.ax.tsv  clean with its four @[kernel_fact] primality proofs (package-specific);
  general/csimp/*.ax.tsv      the csimp add-on (NTMathlibCsimp.lean): csimp-<pkg> with it (general), csimpctl-<pkg> the
                              same facts with library v12 and the same settings but without it (a fact PROVED there counts under
                              library), csimpgate-<pkg> its regression gates (no credits), targets-<pkg> the facts it was run on;
  specific/berry-esseen-v8.ax.tsv  BerryEsseen with the tokenizer add-on (every string-blocked fact except the
                              modules below);
  specific/strings/berry_esseen_strings.tsv  BerryEsseen cover modules converted earlier with the same add-on
                              (one fact per module; module, verdict);
  specific/covers/<tag>/F2_<tag>.log  BerryEsseen covers parsed once (the final check's PROVED line, rc=0);
  specific/types/*.ax.tsv     BobDyLean with NTBobDeq (wt-final3-bob), and runs without it (bobN, bobP1): a fact
                              PROVED without the add-on would count under library;
  specific/addons/<run>.ax.tsv  runs with a package add-on imported (ADDON_RUNS: the lean-regex, Strata and minidregg add-ons on the
                              build with the word-size case split, v8s-r4b3-*-p13c, and minidregg's 4,000-DAG fact on the build before,
                              v8s-r4-md-c4-4000-m120; v13a9-longfellow-zk, v13a9p-longfellow-zk, v13fp-formal-conjectures), and
                              runs without credits (ADDON_GATES: regression runs that re-run every previously proved fact of the
                              package with the add-on; the same add-on facts on earlier builds: v8s-r4-regex-f1,
                              v8s-r4-strata-taut-a1, v8s-r4-strata-taut-p12b, v8s-r4-md-c4-a2);
  options/options_only_conversions.tsv  the facts that the opt-in options convert, by axiom name, with the smallest option set
                              that the controls allow (a summary of the runs below; checked against them, line "options-only list");
  options/<run>/<pkg>__F<k>_<module>_<i>.lean and .log  one prove_native_axiom_nth per fact (fact i of the module,
                              in the order of the study's driver), its config naming the options; the log ends with
                              the exit status (a fact counts if the log has its PROVED line and rc=0); 1500 s and
                              36 GiB per fact, two at a time, on build nt22 (the library modules of v13, Driver/ aside:
                              options/nt22_sources.sha256). Runs: c22s stage; c22c csimp; c22p stage, csimp, propSplit
                              and split 16; c22z the same, importing PrepZcash (four stage_native_axiom_nth commands
                              whose staged values every zcash fact of the run shares; compiled once); c22n the facts
                              of c22p with propSplit and split 16 only (their control); lf22 longfellow-zk with stage,
                              csimp, propSplit and split 16, and its controls lf22k (no stage) and lf22n (no stage, no
                              csimp); lr6 one trainverify fact with all four options and a 3,000 s budget (within the heavy
                              pass's 3,600 s). list.tsv: package directory,
                              file and extra import path of each fact; axcheck/: the axioms of the staged
                              conversions, checked after the runs (no credits); imports/: the study's module that one
                              humanfia fact imports (as in the study's driver).
Regressions: facts PROVED in the study with another verdict in a later run (last line per fact in each run).
The facts new in the library column are also counted by mechanism: the resource techniques (the quick whole-term
attempt and bounded search of the defaults at the study budget, runs v8r; propSplit, runs v8rp; shards) and the
retries (casts, copies in types, iterator-based string functions); a fact proved by sources of two mechanisms is
counted under both names joined by " + " (the controls of the csimp runs only where no other run proves the fact).
The facts new in the options column are counted by their option set; where runs with different option sets prove a
fact, only the smallest sets count (joined by " or "). The facts of the options runs that an earlier column counts are
listed by that column and its mechanism (library) or sources (the other columns).
"""
import collections
import re
import statistics
import sys
from pathlib import Path

M2 = Path('study/results/m2')
SMP = Path('study/results/sample')
BVD = Path('study/results/bv_decide')
AFT = Path('study/results/after')
EXP = ('-remedy', '-fuel')
SAMPLE_OVERRIDE = {'FrederickPu_Zag': 'retry-zag'}
COLS = ('study', 'library', 'general', 'options', 'specific')     # the order of crediting: most general first
NC = len(COLS)
LIB, GEN, OPT, SPEC = (COLS.index(c) for c in ('library', 'general', 'options', 'specific'))
NAMES = {'trainverify': 'TrainVerify', 'cvc5-logos': 'cvc5/logos', 'humanfia-icho2026': 'Humanfia IChO 2026',
         'formal-conjectures': 'formal-conjectures', 'longfellow-zk': 'longfellow-zk',
         'asi-stack-book': 'asi-stack-book', 'rs-mca': 'rs-mca (8 sub-projects)', 'sounio': 'sounio',
         'lido-srv3': 'lido-srv3', 'berry-esseen': 'BerryEsseen', 'strata': 'Strata', 'clean': 'clean',
         'cedar-lean': 'cedar-spec', 'aks': 'aks', 'sorting-network-expanders': 'sorting-network',
         'aeneas-lean': 'aeneas'}
CEDAR = [('corpus', 'cedar-lean'), ('sample', 'cedar_policy_cedar_spec_cedar_lean')]
SPECIAL = {'cedar': CEDAR, 'cedar-lean': CEDAR, 'cedar-nt9c': CEDAR,
           'codegraff': [('sample', 'justrach_codegraff_lean_proofs')],
           'codegraff-nt9c': [('sample', 'justrach_codegraff_lean_proofs')],
           'minidregg': [('sample', 'emberian_minidregg')], 'minidregg-nt9c': [('sample', 'emberian_minidregg')],
           'regex-nt9c': [('sample', 'pandaman64_lean_regex_correctness')],
           'zag': [('sample', 'FrederickPu_Zag')], 'zag-all': [('sample', 'FrederickPu_Zag')],
           'ninegates': [('sample', 'sun123zxy_ninegates_lean4')], 'ninegates-all': [('sample', 'sun123zxy_ninegates_lean4')]}
RUN_PREFIXES = ('v8rp-', 'v8r-', 'v9c-', 'v10c-', 'v11c-', 'v12c-', 'v13c-', 'v14c-', 'v11s-', 'v12s-', 'v13s-', 'v14s-',
                'v8s-', 'v8-', 'v9-', 'v10-', 'v11-', 'v12-', 'v13-', 'v14-')
TYPES = {'wt-final3-zag3': [('sample', 'FrederickPu_Zag')], 'wt-final3-mini': [('sample', 'emberian_minidregg')],
         'wt-final3-miniacc': [('sample', 'emberian_minidregg')]}
BOB = [('sample', 'BobDyLean_bobdylean_paper_artifact')]
BOB_WITH, BOB_WITHOUT = ('wt-final3-bob',), ('wt-v9a-bobN', 'wt-v9b-bobN', 'wt-t2-bobP1')


def pkg_of(name):
    return 'rs-mca' if name.startswith('rs-mca-') else name


def die(msg):
    sys.exit(f'after_table: {msg}')


# ---- the study: corpus (as paper_numbers.py)
rows = {}
for f in sorted((M2 / 'ax').glob('*.ax.tsv')):
    for line in f.read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) < 6:
            continue
        c += [''] * (12 - len(c))
        rows[(c[0], c[1], c[2])] = c
have_mod = {(c[0], c[1]) for c in rows.values() if c[5] != 'NOT_BUILT'}
rows = [c for c in rows.values() if (c[5] != 'NOT_BUILT' or (c[0], c[1]) not in have_mod) and not c[0].endswith(EXP)]


def not_an_equation(c):
    if not (c[5] == 'FAILED' and c[6] == 'other'):
        return False
    for lg in (M2 / 'logs' / c[0]).glob('ax[12]_*.log'):
        t = lg.read_text(errors='ignore')
        if f"FAILED `{c[2]}`" in t and 'does not state an equation' in t:
            return True
    return False


facts = {}      # (set, package, module, axiom) -> study verdict
for c in rows:
    if c[5] != 'NOT_BUILT' and not not_an_equation(c):
        facts[('corpus', c[0], c[1], c[2])] = c[5]
pt = {}
for f in sorted((M2 / 'pertheorem').glob('*.tsv')):
    for line in f.read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) >= 4:
            pt[(c[0], c[1], c[2])] = c
pertheorem = collections.Counter()      # display package -> [facts, converted]; no later source changes them
pt_conv = collections.Counter()
for c in pt.values():
    if c[3] != 'NOT_BUILT':
        pertheorem[pkg_of(c[0])] += 1
        pt_conv[pkg_of(c[0])] += c[3] == 'KERNELIZED'

# ---- the study: random sample (as sample_agg2.py)
for f in sorted(SMP.glob('s_*.ax.tsv')):
    name = f.name[2:-7]
    if name in SAMPLE_OVERRIDE and (SMP / (SAMPLE_OVERRIDE[name] + '.ax.tsv')).exists():
        f = SMP / (SAMPLE_OVERRIDE[name] + '.ax.tsv')
    last = {}
    for line in f.read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) >= 7:
            last[(c[1], c[2])] = c
    for (mod, ax), c in last.items():
        if c[5] != 'NOT_BUILT':
            facts[('sample', name, mod, ax)] = c[5]

packages = {(k[0], k[1]) for k in facts}
by_axiom = collections.defaultdict(list)
by_module = collections.defaultdict(list)
for k in facts:
    by_axiom[k[3]].append(k)
    by_module[(k[0], k[1], k[2])].append(k)

# ---- later sources: (column, label, key) credits, PROVED rows outside the study, regressions
credits = []
outside = collections.Counter()
regress = []
seen = collections.defaultdict(dict)     # key -> {label: verdict}, for the regression notes
pending = []


def check_scopes(scopes, label):
    for s in scopes:
        if s not in packages:
            die(f'{label}: package {s} is not a package of the study')


def read_run(path, scopes, label, col, skip=frozenset()):
    """a per-fact result file: credit PROVED facts of the study (none if col is None; never those in skip), note
    other verdicts of study-PROVED facts"""
    check_scopes(scopes, label)
    last = {}
    for line in Path(path).read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) >= 6:
            last[(c[1], c[2])] = c
    for (mod, ax), c in last.items():
        if ax in ('', '-'):
            continue
        keys = [(s[0], s[1], mod, ax) for s in scopes if (s[0], s[1], mod, ax) in facts]
        for k in keys:
            seen[k][label] = c[5]
            if facts[k] == 'PROVED' and c[5] != 'PROVED':
                regress.append((label, k, c[5], c[6] if len(c) > 6 else ''))
        if c[5] == 'PROVED' and col is not None:
            if keys:
                credits.extend((col, label, k) for k in keys if k not in skip)
            else:
                outside[label] += 1


def run_scope(name):
    for p in RUN_PREFIXES:
        if name.startswith(p):
            t = name[len(p):]
            return SPECIAL.get(t) or ([('sample', t[2:])] if t.startswith('s_') else [('corpus', t)])
    die(f'run {name}: unknown family')


# library: per-fact runs of v8-v13, copies in types, shards; the high-cap re-runs (HIGHCAP: run name -> scopes)
HIGHCAP = AFT / 'library' / 'highcap' / 'C_final.tsv'    # one row per fact: tag, package, module, axiom, ..., verdict, reason, secs, peak_kb
HEAVY_KIB, HEAVY_S = 96 * 1048576, 3600
highcap_over = {}      # key -> peak KiB of facts PROVED only above the heavy pass's limits
as96_failed = set()    # of those: facts that a re-run under a hard 96 GiB address-space cap did not prove
hc_verdicts = collections.Counter()
if HIGHCAP.exists():
    hrows = [l.split('\t') for l in HIGHCAP.read_text(errors='ignore').splitlines() if l.strip()]
    ix = {h: n for n, h in enumerate(hrows[0])}
    for c in hrows[1:]:
        c += [''] * (len(hrows[0]) - len(c))
        pkg, verdict = c[ix['package']], c[ix['verdict']]
        hc_verdicts[verdict] += 1
        scopes = [('sample', pkg[2:])] if pkg.startswith('s_') else [('corpus', pkg)]
        check_scopes(scopes, 'high-cap re-runs')
        keys = [(s[0], s[1], c[ix['module']], c[ix['axiom']]) for s in scopes if (s[0], s[1], c[ix['module']], c[ix['axiom']]) in facts]
        for k in keys:
            seen[k]['high-cap re-runs'] = verdict
            if facts[k] == 'PROVED' and verdict != 'PROVED':
                regress.append(('high-cap re-runs', k, verdict, c[ix['reason']]))
        if verdict != 'PROVED' or not keys:
            continue
        peak = int(c[ix['peak_kb']]) if c[ix['peak_kb']].isdigit() else None
        secs = float(c[ix['secs']]) if c[ix['secs']].replace('.', '', 1).isdigit() else None
        as96 = c[ix['as96_verdict']] if 'as96_verdict' in ix else ''
        if as96:
            fits = as96 == 'PROVED'      # the exact test: a hard 96 GiB address-space cap within 3,600 s
        else:
            fits = peak is not None and secs is not None and peak <= HEAVY_KIB and secs <= HEAVY_S
        if fits:
            credits.extend((LIB, 'highcap re-runs', k) for k in keys)
        else:
            for k in keys:
                highcap_over[k] = max(highcap_over.get(k, 0), peak or 0)
                if as96:
                    as96_failed.add(k)
else:
    pending.append('high-cap re-runs (facts with a single piece above 48 GiB): table not in the artifact yet')
runs = sorted((AFT / 'library' / 'runs').glob('*.ax.tsv'))
if not runs:
    die('no library runs')
for f in runs:
    read_run(f, run_scope(f.name[:-7]), f.name[:-7], 1)
for name, scopes in TYPES.items():
    read_run(AFT / 'library' / 'types' / f'{name}.ax.tsv', scopes, name, 1)
for comb in sorted((AFT / 'library' / 'shards').glob('*/Comb_*.log')):
    tag = comb.parent.name
    cmd = comb.parent / 'cmd.txt'
    m = re.search(r'prove_native_axiom_nth (\S+) \d+', cmd.read_text()) if cmd.exists() else None
    for ax in sorted(set(re.findall(r'^PROVED `([^`]+)` as `_ktshard\.', comb.read_text(errors='ignore'), re.M))):
        keys = [k for k in by_axiom.get(ax, []) if m is None or k[2] == m.group(1)]
        if keys:
            credits.extend((1, f'shard {tag}', k) for k in keys)
        else:
            outside[f'shard {tag}'] += 1
for line in (AFT / 'library' / 'shard_conversions.tsv').read_text().splitlines():
    c = line.split('\t')
    if len(c) >= 14 and c[13] == 'shards' and c[9] == 'PROVED':
        k = (c[0], c[1][2:] if c[1].startswith('s_') else c[1], c[2], c[3])
        if k in facts:
            credits.append((1, 'shard (earlier pass)', k))
        else:
            outside['shard (earlier pass)'] += 1

# general add-ons: bv_decide route, csimp
sweep = [l.split('\t') for l in (BVD / 'sweep' / 'final_per_fact.tsv').read_text().splitlines()]
hdr = sweep[0]
sweep = [dict(zip(hdr, r)) for r in sweep[1:]]
f9 = [l.split('\t') for l in (BVD / 'final9.tsv').read_text().splitlines()]
f9 = {(r[1], r[2]) for r in f9[1:]}       # (module, axiom_index)
for r in sweep:
    if 'CONVERTED' in (r['lrat_verdict'], r['bvs4_verdict']) or (r['module'], r['idx']) in f9:
        k = ('sample', r['pkg'][2:], r['module'], r['axiom']) if r['pkg'].startswith('s_') else \
            ('corpus', r['pkg'], r['module'], r['axiom'])
        if k in facts:
            credits.append((2, 'bv_decide route', k))
        else:
            outside['bv_decide route'] += 1
# package-specific: clean's four norm_num primality proofs of its own prime constants (study/remedies/clean)
read_run(M2 / 'ax' / 'clean-remedy.ax.tsv', [('corpus', 'clean')], 'primality proofs (clean)', SPEC)
CS = AFT / 'general' / 'csimp'
scope_of = lambda t: SPECIAL.get(t) or ([('sample', t[2:])] if t.startswith('s_') else [('corpus', t)])


def opt_label(opts):
    """option names in a fixed order: stage, csimp, propSplit, split N, then the rest"""
    key = lambda o: (next((i for i, n in enumerate(('stage', 'csimp', 'propSplit', 'split')) if o.split(' ')[0] == n), 4), o)
    return ' + '.join(sorted(opts, key=key))


ctl = set()
for f in sorted(CS.glob('csimpctl-*.ax.tsv')):
    name = f.name[:-7]
    read_run(f, scope_of(name[len('csimpctl-'):]), name, 1)
    ctl |= {k for k in seen if seen[k].get(name) == 'PROVED'}
for f in sorted(CS.glob('csimpgate-*.ax.tsv')):
    name = f.name[:-7]
    read_run(f, scope_of(name[len('csimpgate-'):]), name, None)
csimp = sorted(CS.glob('csimp-*.ax.tsv'))
for f in csimp:
    name = f.name[:-7]
    read_run(f, scope_of(name[len('csimp-'):]), name, 2)
csimp_proved = {k for k in seen if any(l.startswith('csimp-') and v == 'PROVED' for l, v in seen[k].items())}
if not csimp:
    pending.append('csimp add-on: no results yet (general/csimp/)')

# package-specific add-ons: BerryEsseen (tokenizer add-on, parse-once covers), NTBobDeq
BE = [('corpus', 'berry-esseen')]
read_run(AFT / 'specific' / 'berry-esseen-v8.ax.tsv', BE, 'BerryEsseen tokenizer add-on', SPEC)
be_tried = {k for k in seen if k[:2] == BE[0] and 'BerryEsseen tokenizer add-on' in seen[k]}
st = [l.split('\t') for l in (AFT / 'specific' / 'strings' / 'berry_esseen_strings.tsv').read_text().splitlines()]
for r in st[1:]:
    keys = by_module.get(('corpus', 'berry-esseen', 'BerryEsseen.Upper0423.' + r[0]), [])
    if len(keys) != 1:
        die(f'strings module {r[0]}: {len(keys)} study facts')
    be_tried.add(keys[0])
    if r[4] == 'PROVED':
        credits.append((SPEC, 'BerryEsseen tokenizer add-on (earlier modules)', keys[0]))
for log in sorted((AFT / 'specific' / 'covers').glob('*/F2_*.log')):
    t = log.read_text(errors='ignore')
    if not re.search(r'^rc=0$', t, re.M):
        continue
    for ax in set(re.findall(r'^PROVED `([^`]+)` as ', t, re.M)):
        keys = [k for k in by_axiom.get(ax, []) if k[:2] == BE[0]]
        be_tried.update(keys)
        if keys:
            credits.extend((SPEC, 'BerryEsseen covers parsed once', k) for k in keys)
        else:
            outside['BerryEsseen covers parsed once'] += 1
for name in BOB_WITHOUT:
    read_run(AFT / 'specific' / 'types' / f'{name}.ax.tsv', BOB, name + ' (without NTBobDeq)', 1)
for name in BOB_WITH:
    read_run(AFT / 'specific' / 'types' / f'{name}.ax.tsv', BOB, 'NTBobDeq', SPEC)

# package add-ons of the later runs: runs with the add-on imported (credits) and regression runs with it (no credits)
ADDON_RUNS = {'v8s-r4b3-regex-p13c': ('lean-regex add-on', [('sample', 'pandaman64_lean_regex_correctness')]),
              'v8s-r4b3-strata-taut-p13c': ('Strata add-on', [('corpus', 'strata')]),
              'v13a9-longfellow-zk': ('longfellow-zk add-on', [('corpus', 'longfellow-zk')]),
              'v13a9p-longfellow-zk': ('longfellow-zk add-on', [('corpus', 'longfellow-zk')]),
              'v13fp-formal-conjectures': ('formal-conjectures primes add-on', [('corpus', 'formal-conjectures')]),
              'v8s-r4b3-md-c4-p13c': ('minidregg add-on', [('sample', 'emberian_minidregg')]),
              'v8s-r4-md-c4-4000-m120': ('minidregg add-on', [('sample', 'emberian_minidregg')])}
ADDON_GATES = {'v13al9-longfellow-zk': [('corpus', 'longfellow-zk')], 'v13af-formal-conjectures': [('corpus', 'formal-conjectures')],
               'v8s-r4-regex-f1': [('sample', 'pandaman64_lean_regex_correctness')], 'v8s-r4-strata-taut-a1': [('corpus', 'strata')],
               'v8s-r4-strata-taut-p12b': [('corpus', 'strata')], 'v8s-r4-md-c4-a2': [('sample', 'emberian_minidregg')]}
HELD = ('', [], ())     # an add-on whose runs are reported but not counted (none since the minidregg add-on ships, 2026-10-25)
for name, (label, scopes) in ADDON_RUNS.items():
    f = AFT / 'specific' / 'addons' / f'{name}.ax.tsv'
    if f.exists():
        read_run(f, scopes, label, SPEC)
    else:
        pending.append(f'{label}: run {name} not in the artifact yet')
for name, scopes in ADDON_GATES.items():
    f = AFT / 'specific' / 'addons' / f'{name}.ax.tsv'
    if f.exists():
        read_run(f, scopes, name + ' (regression run with the add-on)', None)
    else:
        pending.append(f'regression run {name} not in the artifact yet')
held_label, held_scopes, held_runs = HELD
for name in held_runs:
    f = AFT / 'specific' / 'excluded' / f'{name}.ax.tsv'
    if f.exists():
        read_run(f, held_scopes, f'held: {name}', None)
held = {k for k in seen if any(l.startswith('held: ') and v == 'PROVED' for l, v in seen[k].items())}

# library v13 with opt-in options: single-fact runs (options/<run>/*.lean with their .log)
opt_sets = collections.defaultdict(set)     # key -> option sets (frozensets of names) of the runs that prove it
opt_runs = sorted(d for d in (AFT / 'options').glob('*') if d.is_dir() and d.name not in ('imports', 'axcheck'))
for d in opt_runs:
    unfinished = 0
    for lean in sorted(d.glob('*.lean')):
        t = lean.read_text(errors='ignore')
        m = re.search(r'^prove_native_axiom_nth (\S+) \d+ \(config := \{([^}]*)\}\)', t, re.M)
        if not m:
            continue        # a module of shared staged values (stage_native_axiom_nth)
        log = lean.with_suffix('.log')
        lt = log.read_text(errors='ignore') if log.exists() else ''
        if not re.search(r'^rc=\d+', lt, re.M):
            unfinished += 1
            continue
        if not re.search(r'^rc=0\b', lt, re.M):
            continue
        pm = re.match(r'(.+?)__F\d+_', lean.name)
        if not pm:
            die(f'{lean}: no package in the file name')
        scopes = scope_of(pm.group(1))
        check_scopes(scopes, f'options/{d.name}')
        opts = set()
        for item in m.group(2).split(','):
            kv = [x.strip() for x in item.split(':=')]
            if len(kv) != 2 or kv[0] == 'trace' or kv[1] == 'false':
                continue
            opts.add(kv[0] if kv[1] == 'true' else f'{kv[0]} {kv[1]}')
        if any((d / f'{imp}.lean').exists() for imp in re.findall(r'^import (\S+)', t, re.M)):
            opts.add('shared staged module')
        opts = frozenset(opts)
        label = f'{d.name}: ' + opt_label(opts)
        mod = m.group(1).replace('\u00ab', '').replace('\u00bb', '')    # the study writes FormalConjectures.OEIS.115366
        for ax in sorted(set(re.findall(r'^PROVED `([^`]+)` as ', lt, re.M))):
            keys = [(s[0], s[1], mod, ax) for s in scopes if (s[0], s[1], mod, ax) in facts]
            if not keys:
                outside[label] += 1
            for k in keys:
                seen[k][label] = 'PROVED'
                credits.append((OPT, label, k))
                opt_sets[k].add(opts)
    if unfinished:
        pending.append(f'options/{d.name}: {unfinished} runs without their exit status (still running when staged)')
if not opt_runs:
    pending.append('opt-in options: no results yet (options/)')

# ---- the columns: a fact counts in the first column whose sources prove it
first = {k: 0 for k, v in facts.items() if v == 'PROVED'}
via = collections.defaultdict(set)
for col in range(1, NC):
    for c, label, k in credits:
        if c == col:
            via[k].add(label)
            first.setdefault(k, col)
new = collections.Counter(first[k] for k in first if facts[k] != 'PROVED')
gain = collections.Counter((c, label) for c, label, k in set(credits) if first.get(k) == c and facts[k] != 'PROVED')
be_open = sum(1 for k in facts if k[:2] == BE[0] and k not in first and k not in be_tried)
notes = {('corpus', NAMES['berry-esseen']): f'{be_open} facts not converted and without a result yet from the '
                                          'tokenizer add-on or the covers' if be_open else ''}


def mechanism(label):
    if label.startswith('v8r-'):
        return 'resources: quick attempt and bounded search (defaults)'
    if label.startswith('v8rp-'):
        return 'resources: propSplit'
    if label.startswith('shard'):
        return 'resources: shards'
    if label == 'highcap re-runs':
        return 'resources: re-runs with 3,600 s and up to 96 GiB'
    if label == 'v13c-humanfia-icho2026':   # despite its prefix, the high-cap re-run of one Humanfia fact (propSplit, up to 200 GiB)
        return 'resources: re-runs with 3,600 s and up to 96 GiB'
    if label.startswith(('v9c-', 'v10c-', 'v11c-', 'v12c-', 'v13c-', 'v14c-')):
        return 'retries: casts'
    if label.startswith('wt-') or label.endswith(('-zag', '-zag-all')):
        return 'retries: copies in types'
    if label.startswith('v14s-ninegates'):
        return 'retries: word-size case split'
    if label.startswith(('v8s-', 'v11s-', 'v12s-', 'v13s-', 'v14s-')):
        return 'retries: iterator-based string functions'
    if label.startswith('csimpctl-'):
        return 'resources: library v12 with the settings of the csimp runs (their controls)'
    return 'regression gates'


CTL_MECH = 'resources: library v12 with the settings of the csimp runs (their controls)'


def mech_of(k):
    ms = {mechanism(l) for c, l, kk in credits if c == 1 and kk == k}
    return ' + '.join(sorted(ms - {CTL_MECH} if len(ms) > 1 else ms))   # a control only re-proves what another run proved


mech = {k: mech_of(k) for k in first if first[k] == 1}
mech_tally = collections.Counter((k[0], m) for k, m in mech.items())


def opt_of(k):
    sets = opt_sets[k]
    return ' or '.join(sorted(opt_label(s) for s in sets if not any(o < s for o in sets)))


mech.update({k: opt_of(k) for k in first if first[k] == OPT})
opt_tally = collections.Counter((k[0], opt_of(k)) for k in first if first[k] == OPT)


def display(s, pkg):
    return NAMES.get(pkg_of(pkg), pkg_of(pkg)) if s == 'corpus' else pkg


table = collections.defaultdict(lambda: [0] * (1 + NC))      # (set, display) -> facts, cumulative columns
for k in facts:
    t = table[(k[0], display(k[0], k[1]))]
    t[0] += 1
    for col in range(NC):
        t[1 + col] += k in first and first[k] <= col
for p, n in pertheorem.items():
    t = table[('corpus', NAMES.get(p, p))]
    t[0] += n
    for col in range(NC):
        t[1 + col] += pt_conv[p]

out = []
for s in ('corpus', 'sample'):
    ps = [p for (s2, p) in table if s2 == s]
    if s == 'corpus':
        ps.sort(key=lambda p: (-(table[(s, p)][1] / table[(s, p)][0] >= 0.5), -table[(s, p)][0]))
    else:
        ps.sort(key=lambda p: (-table[(s, p)][0], p))
    for p in ps:
        out.append((s, p, table[(s, p)], notes.get((s, p), '')))
    allp = [table[(s, p)] for p in ps]
    largest = max(ps, key=lambda p: table[(s, p)][0])
    groups = [(f'{s}: all {len(ps)} packages', ps), (f'{s}: without {largest}', [p for p in ps if p != largest])]
    if s == 'corpus':
        top3 = sorted(ps, key=lambda p: -table[(s, p)][0])[:3]
        groups.append((f'{s}: without the three largest ({", ".join(top3)})', [p for p in ps if p not in top3]))
    for label, sel in groups:
        tot = [sum(table[(s, p)][i] for p in sel) for i in range(1 + NC)]
        out.append((s, label, tot, ''))
    for stat, fn in (('per-package median rate', statistics.median), ('per-package mean rate', statistics.mean)):
        out.append((s, stat, [None] + [fn([t[1 + c] / t[0] for t in allp]) for c in range(NC)], ''))
    for (s2, m), n in sorted(mech_tally.items()):
        if s2 == s:
            out.append((s, f'library by mechanism: {m}', [None] * (1 + NC), f'{n} facts new in the library column'))
    for (s2, m), n in sorted(opt_tally.items()):
        if s2 == s:
            out.append((s, f'options by option set: {m}', [None] * (1 + NC), f'{n} facts new in the options column'))
held_new = sorted(k for k in held if k not in first)
if held_runs and held:
    pending.append(f'{held_label}: {len(held)} facts PROVED with it ({len(held_new)} converted by nothing else), not counted')
out.append(('all', 'pending sources', [None] * (1 + NC), '; '.join(pending) or 'none'))


def fmt(v, n):
    return f'{v:,}' if n is None else f'{v:,} ({100 * v / n:.2f}%)'


print('facts converted per package; columns are cumulative: ' + ' -> '.join(COLS))
print('set\tpackage\tfacts\t' + '\t'.join(COLS) + '\tnotes')
for s, p, t, n in out:
    if t[1] is None:
        print(f'{s}\t{p}' + '\t' * (2 + NC) + n)
    elif t[0] is None:
        print(f'{s}\t{p}\t\t' + '\t'.join(f'{100 * x:.2f}%' for x in t[1:]) + f'\t{n}')
    else:
        print(f'{s}\t{p}\t{t[0]:,}\t' + '\t'.join(fmt(x, t[0]) for x in t[1:]) + f'\t{n}')
print('\nnew conversions per column (each fact once, in its first column), and the sources that prove them (a fact '
      'can have several):')
for c in range(1, NC):
    print(f'  {COLS[c]}: {new[c]:,} facts; ' + ', '.join(f'{label} {n:,}' for (cc, label), n in sorted(gain.items())
                                                        if cc == c))
# the resource failures outside the author's own package (library/shard_conversions.tsv: one line per fact; column 7
# where the study's check died, column 9 the tactic) and their re-runs at the study's limits (runs v8r, v8rp, shards)
rf = {}
for line in (AFT / 'library' / 'shard_conversions.tsv').read_text().splitlines():
    c = line.split('\t')
    if len(c) >= 9:
        rf[(c[0], c[1][2:] if c[1].startswith('s_') else c[1], c[2], c[3])] = c
if any(k not in facts for k in rf):
    die('shard_conversions.tsv: facts outside the study')
died = collections.Counter(c[6] for c in rf.values())
search = collections.Counter(f'{c[4]}/{c[5]}' for c in rf.values() if c[6] == 'search')
print(f"\nresource failures outside the author's own package: {len(rf)} (corpus {sum(k[0] == 'corpus' for k in rf)}, "
      f"sample {sum(k[0] == 'sample' for k in rf)}); died in the search for split points {died['search']} (" +
      ', '.join(f'{v} {n}' for v, n in search.most_common()) + f"), in the kernel {died['kernel']}; "
      f"bv_decide {sum(c[8] == 'bv_decide' for c in rf.values())}")
rerun = {k for k in rf if any(l.startswith('v8r-') for l in seen.get(k, {}))}      # the selected facts, not inner ones
pa = {k for k in rerun if seen[k].get(next(l for l in seen[k] if l.startswith('v8r-'))) == 'PROVED'}
pb = {k for k in rerun if any(l.startswith('v8rp-') and v == 'PROVED' for l, v in seen[k].items())} - pa
sharded = {k for c, l, k in credits if l.startswith('shard shard_')} & rerun - pa - pb
pieces = [int(x) for comb in (AFT / 'library' / 'shards').glob('*/Comb_*.log')
          if re.search(r'^PROVED ', comb.read_text(errors='ignore'), re.M)
          for x in re.findall(r'pieces=(\d+)', comb.read_text(errors='ignore'))]
print(f"re-run at the study's limits: {len(rerun)} facts; converted {len(pa | pb | sharded)}: {len(pa | pb)} with the "
      f"defaults or the structured checks (defaults {len(pa)}, propSplit {len(pb)}), {len(sharded)} sharded "
      f"(up to {max(pieces) if pieces else 0} pieces)")
lib = {k for k in rf if first.get(k) == 1}
prim = {k for c, l, k in credits if l == 'primality proofs (clean)' and first.get(k) == SPEC} & set(rf)
bvd = {k for k, c in rf.items() if c[8] == 'bv_decide'}
print(f"the {len(rf)} now: kernel proofs {len(lib | prim)} (library {len(lib)}, clean's primality proofs {len(prim)}), "
      f"bv_decide {sum(first.get(k) == 2 for k in bvd)} of {len(bvd)} converted by its route, remaining "
      f"{len(set(rf) - lib - prim - {k for k in bvd if first.get(k) == 2})}")
rem = set(rf) - lib - prim - {k for k in bvd if first.get(k) == 2}
print(f'of these {len(rem)}: converted by the opt-in options {sum(first.get(k) == OPT for k in rem)}, by package add-ons '
      f'{sum(first.get(k) == SPEC for k in rem)}, by a general add-on {sum(first.get(k) == GEN for k in rem)}; in no column '
      f'{sum(1 for k in rem if k not in first)} ({sum(1 for k in rem if k not in first and k in highcap_over)} of them PROVED with up to '
      f'200 GiB and 3,600 s)')
print(f'csimp add-on: {len(csimp_proved)} facts of the study PROVED with it, {len(csimp_proved & ctl)} of them also by its control '
      f'(library v12 without it: these count under library if new), '
      f'{sum(1 for k in csimp_proved - ctl if first.get(k) == 2 and any(l.startswith("csimp-") for l in via[k]))} new in the general column')
opt_proved = set(opt_sets)
print(f'opt-in options: {len(opt_proved)} facts of the study PROVED in the single-fact runs, '
      f'{sum(1 for k in opt_proved if first[k] < OPT)} of them counted in an earlier column, '
      f'{sum(1 for k in opt_proved if first[k] == OPT)} new in the options column')


def first_sources(k):
    """the mechanism (library) or the sources (other columns) that put a fact in its first column"""
    if first[k] == 1:
        return mech[k]
    return ' + '.join(sorted({l for c, l, kk in credits if kk == k and c == first[k]}))


earlier = collections.Counter((first[k], first_sources(k)) for k in opt_proved if 0 < first[k] < OPT)
print('opt-in options, counted in an earlier column: ' + '; '.join(
    f'{COLS[c]} {sum(n for (cc, _), n in earlier.items() if cc == c)} (' +
    ', '.join(f'{s} {n}' for (cc, s), n in sorted(earlier.items(), key=lambda x: (-x[1], x[0][1])) if cc == c) + ')'
    for c in sorted({c for c, _ in earlier})))
newopt = collections.Counter((k[0], display(k[0], k[1]), opt_of(k)) for k in opt_proved if first[k] == OPT)
print('opt-in options, new facts by package and option set: ' +
      ('; '.join(f'{p} {o} {n}' for (s, p, o), n in sorted(newopt.items())) or 'none'))
colsets = collections.defaultdict(set)
for c, l, k in credits:
    colsets[k].add(c)
multi = collections.Counter(' + '.join(COLS[c] for c in sorted(cs)) for k, cs in colsets.items()
                            if len(cs) > 1 and facts.get(k) != 'PROVED')
print('facts new after the study that sources of two or more columns convert (counted in the first): ' +
      (', '.join(f'{m} {n}' for m, n in sorted(multi.items())) or 'none'))
if held_runs:
    print(f'held, not counted: {held_label}: {len(held)} facts PROVED with it, {len(held_new)} of them converted by nothing else' +
      (' (' + ', '.join(f"{k[1]} {k[3].split('.')[-4] if k[3].count('.') >= 4 else k[3]}" for k in held_new) + ')' if held_new else ''))
hc_lib = {k for c, l, k in credits if l == 'highcap re-runs' and first.get(k) == LIB and facts[k] != 'PROVED'}
hc_more = sorted((k, kib) for k, kib in highcap_over.items() if k not in first)
if hc_verdicts:
    print(f'high-cap re-runs (one piece above 48 GiB; up to 3,600 s, caps up to 200 GiB; {sum(hc_verdicts.values())} facts: ' +
          ', '.join(f'{v} {n}' for v, n in sorted(hc_verdicts.items())) + f'): {len(hc_lib)} new within 3,600 s and 96 GiB (counted '
          f'under library); with up to 200 GiB and 3,600 s: {len(hc_more)} more' +
          (f' (resident peaks {min(v for _, v in hc_more) / 1048576:.1f}-{max(v for _, v in hc_more) / 1048576:.1f} GiB'
           + (f'; {sum(1 for k, _ in hc_more if k in as96_failed)} of them not proved under a hard 96 GiB cap'
              if any(k in as96_failed for k, _ in hc_more) else '') + '; in no column)' if hc_more else ''))
OOL = AFT / 'options' / 'options_only_conversions.tsv'
if OOL.exists():
    def ool_set(label):
        base = re.sub(r'\s*\([^)]*\)', '', label).split(',')[0]
        s = {x.strip() for x in base.split('+') if x.strip()}
        if 'shared staging module' in label:
            s.add('shared staged module')
        return frozenset(s)
    lrows = [l.split('\t') for l in OOL.read_text().splitlines()[1:] if l.strip()]
    agree, differ, absent = 0, [], []
    for c in lrows:
        scopes = [('sample', c[0][2:])] if c[0].startswith('s_') else [('corpus', c[0])]
        keys = [k for k in by_axiom.get(c[1], []) if k[:2] in scopes]
        if not keys or keys[0] not in opt_sets:
            absent.append(c[1].split('.')[-4] if c[1].count('.') >= 4 else c[1])
            continue
        sets = opt_sets[keys[0]]
        mine = {s for s in sets if not any(o < s for o in sets)}
        if mine == {ool_set(c[2])}:
            agree += 1
        else:
            differ.append(f"{c[1].split('.')[-4] if c[1].count('.') >= 4 else c[1]}: list {opt_label(ool_set(c[2]))}, runs " +
                          ' or '.join(sorted(opt_label(s) for s in mine)))
    print(f'options-only list: {len(lrows)} facts; smallest option set as in the runs here for {agree}' +
          (f'; differs for {len(differ)} ({"; ".join(differ)})' if differ else '') +
          (f'; not among the runs here: {len(absent)} ({", ".join(absent)})' if absent else ''))
print('PROVED rows for facts outside the study (not counted): ' +
      (', '.join(f'{l} {n}' for l, n in sorted(outside.items())) or 'none'))
bob_lib = [k for c, l, k in credits if l.endswith('(without NTBobDeq)')]
print(f'BobDyLean facts PROVED without NTBobDeq: {len(set(bob_lib))}')
reg = sorted({(l, k, v, r) for l, k, v, r in regress})
print(f'regressions (PROVED in the study, another verdict in a later run): {len(reg)} rows, '
      f'{len({k for _, k, _, _ in reg})} facts')
for l, k, v, r in reg[:20]:
    later = sorted(x for x, vv in seen[k].items() if vv == 'PROVED')
    print(f'  {l}\t{k[1]}\t{k[3]}\t{v} {r}\tPROVED in: {", ".join(later) or "-"}')

a = sys.argv[1:]
opt = lambda o: a[a.index(o) + 1] if o in a else None
if opt('--tsv'):
    with open(opt('--tsv'), 'w') as fo:
        fo.write('set\tpackage\tfacts\t' + '\t'.join(COLS) + '\t' + '\t'.join(f'rate_{c}' for c in COLS) + '\tnotes\n')
        for s, p, t, n in out:
            if t[1] is None:
                fo.write(f'{s}\t{p}' + '\t' * (2 + 2 * NC) + f'{n}\n')
            elif t[0] is None:
                fo.write(f'{s}\t{p}' + '\t' * (2 + NC) + '\t'.join(f'{100 * x:.2f}%' for x in t[1:]) + f'\t{n}\n')
            else:
                fo.write(f'{s}\t{p}\t{t[0]}\t' + '\t'.join(str(x) for x in t[1:]) + '\t' +
                         '\t'.join(f'{100 * x / t[0]:.2f}%' for x in t[1:]) + f'\t{n}\n')
if opt('--facts'):
    with open(opt('--facts'), 'w') as fo:
        fo.write('set\tpackage\tmodule\taxiom\tstudy_verdict\tcolumn\tmechanism\tsources\n')
        for k in sorted(k for k in first if first[k] > 0):
            fo.write('\t'.join(k) + f'\t{facts[k]}\t{COLS[first[k]]}\t{mech.get(k, "")}\t' + '; '.join(sorted(via[k])) + '\n')
if opt('--regressions'):
    with open(opt('--regressions'), 'w') as fo:
        fo.write('run\tset\tpackage\tmodule\taxiom\tverdict\treason\tPROVED_in\n')
        for l, k, v, r in reg:
            later = sorted(x for x, vv in seen[k].items() if vv == 'PROVED')
            fo.write(f'{l}\t' + '\t'.join(k) + f'\t{v}\t{r}\t' + ', '.join(later) + '\n')
