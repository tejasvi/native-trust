#!/usr/bin/env python3
"""v3_numbers_v10.py (2026-10-30; v9 + detail 'does not state an equation' for such sample facts).
v3_numbers_v9.py (2026-10-29; v8 + axioms that do not state an equation are left out of the corpus only: the
study's sample rule (sample_agg2.py) counts them, as in its 2,018 facts).
v3_numbers_v8.py (2026-10-29; v7 + facts_D.tsv gains the study's verdict and reason of each fact).
v3_numbers_v7.py (2026-10-29; v6 + deterministic output order: facts in sorted order, ties sorted by name; v6's
order of equal counts depended on Python's hash seed).
v3_numbers_v6.py (2026-10-29; v5 + inputs from the artifact alone and a check mode; the sample's baseline is the
study's as the paper reports it: Zag from retry-zag, the other runs as run (index row RS6), where v3-v5 used
sample_agg2.py's default overrides). Options:
  --res-extra DIR       more folders with result files (searched after RESULTS; a name found twice is an error)
  WORK = -              no work tree: then --axiom-index FILE (base, module, axiom, index; .gz or plain) maps a fact to
                        its log name, and --logs DIR holds the logs as DIR/<work dir>/<log name>.gz (or plain)
  --study-pt DIR        the study's per-theorem rs-mca files (default: the --study-m2 folder)
  --check DIR           compute in memory and compare every output with DIR/<name>; OUT may then be '-'; exit 1 on a
                        difference; writes nothing.
v3_numbers_v5.py (2026-10-29; v4 + facts_D.tsv: every fact with its final D row and its column flags).
v3_numbers_v4.py (2026-10-29; v3 + facts_not_converted_D.tsv gains tactic, inner, detail (what the check log says
stopped the kernel), secs and maxrss_kb; map_used's not_in_D leaves out NOT_BUILT rows).
v3_numbers_v3.py (2026-10-29; v2 + a fact proved in any D pass counts as converted and otherwise its verdict is the
last row that is not a harness failure (in the later passes every driver run re-runs all phase-1 inner facts); per-fact
comparison with the study's verdicts (regress_D.tsv; per_package.tsv gains the study's count, regressions and gains)).
v3_numbers_v2.py (2026-10-29; v1 + explicit column map, the heavy-pass order of the pass runner's selection, exact check
logs per pass, and a check for harness failures left in the final rows): the v3 evaluation's numbers (one library
version, the archived final library) from the v3 result files, with the study's counting rules
(study/aggregators/paper_numbers.py, m2_aggregate_ax.py and sample_agg2.py): the last line per (run, module, axiom)
of a pass counts; NOT_BUILT lines are modules that did not build (left out unless the module has facts); axioms that
do not state an equation are left out (their log says so); rs-mca's Lean 4.28 sub-projects are counted per theorem
from m2_repo4.py (verdict KERNELIZED), as in the study. Each sample run is one package, as in sample_agg2.py.

Passes, per base run B (the study's run name), in this order; a fact's verdict is its last row over the passes of a
column, and a fact converted in an earlier column stays converted:
  D (the final library at the study's protocol): v3-B, v3r-B (harness redo at 900 s / 48 GiB), then the heavy pass
    v3h-B (memory, 96 GiB), v3h-B_t (timeouts), v3h-B_b (bv_decide timeouts), v3h-B_r (harness redo of _t and _b);
  G: + general add-ons;  P: + v3p-B (propSplit);  O: + v3o-B (opt-in options);  K: + package add-ons
  (v4 order; v1-v3 had D, P, O, G, K).
Files of P, O, G and K beyond v3p-B and v3o-B are named in --map FILE, lines COL<TAB>BASE<TAB>STEM (results
RESULTS/STEM.ax.tsv, the driver's 12 columns; '#' lines skipped).
Harness failure (as in the pass runner's selection): an ERROR row of a pass whose processes a unit can kill (v3, v3r at
900 s; v3h_t, v3h_b at 3,600 s) whose check log ends with rc 137/-9 before the limit and has no out-of-memory message,
or an ERROR rc143/rc-15 row. The final D rows must hold none; any left are listed in harness_D.tsv.
Run on the box as ntbuild (it reads the logs under WORK).

usage: v3_numbers_v6.py AGG_DIR RESULTS WORK OUT [--map FILE] [--study-m2 DIR] [--study-sample DIR] [--study-pt DIR]
                        [--res-extra DIR]... [--axiom-index FILE] [--logs DIR] [--check DIR]
  AGG_DIR = the artifact's study/aggregators (for m2_aggregate2.construct); OUT = output folder (created, must not exist).
Writes OUT/summary.txt, per_package.tsv, verdicts_D.tsv, classes_D.tsv, facts_not_converted_D.tsv, harness_D.tsv,
factlist_diff.tsv, map_used.tsv, regress_D.tsv, facts_D.tsv.
"""
import collections, gzip, io, re, statistics, sys
from pathlib import Path

args = sys.argv[1:]
def opt(name, many=False):
    vals = [args[i + 1] for i, a in enumerate(args) if a == name]
    return vals if many else (vals[0] if vals else None)
pos = [a for i, a in enumerate(args) if not a.startswith('--') and (i == 0 or not args[i - 1].startswith('--'))]
if len(pos) < 4:
    sys.exit(__doc__)
AGG, RES = Path(pos[0]), Path(pos[1])
WORK = None if pos[2] == '-' else Path(pos[2])
OUT = None if pos[3] == '-' else Path(pos[3])
RES_DIRS = [RES] + [Path(p) for p in opt('--res-extra', True)]
MAP = Path(opt('--map')) if opt('--map') else None
STUDY_M2 = Path(opt('--study-m2')) if opt('--study-m2') else None
STUDY_S = Path(opt('--study-sample')) if opt('--study-sample') else None
STUDY_PT = Path(opt('--study-pt')) if opt('--study-pt') else STUDY_M2
AXIDX = Path(opt('--axiom-index')) if opt('--axiom-index') else None
LOGS = Path(opt('--logs')) if opt('--logs') else None
CHECK = Path(opt('--check')) if opt('--check') else None
if WORK is None and (AXIDX is None or LOGS is None):
    sys.exit('WORK = - needs --axiom-index and --logs')
if CHECK is None:
    if OUT is None:
        sys.exit('OUT = - only with --check')
    for p in RES_DIRS + [x for x in (WORK, LOGS) if x is not None]:
        if OUT.resolve() == p.resolve() or p.resolve() in OUT.resolve().parents:
            sys.exit(f'refusing: {OUT} is inside the input dir {p}')
    if OUT.exists():
        sys.exit(f'{OUT} exists')
OUTPUTS = {}   # output file name -> list of text pieces; written (or checked) at the end


class _Out:
    def __init__(self, name):
        self.name = name
        OUTPUTS[name] = []
    def write(self, s):
        OUTPUTS[self.name].append(s)
    def __enter__(self):
        return self
    def __exit__(self, *a):
        return False


def outw(name):
    return _Out(name)


def find_res(name):
    hits = [d / name for d in RES_DIRS if (d / name).exists()]
    if len(hits) > 1:
        sys.exit(f'{name} found in more than one results folder: {hits}')
    return hits[0] if hits else RES_DIRS[0] / name


sys.path.insert(0, str(AGG))
from m2_aggregate2 import construct  # noqa: E402

BLOCKER_RE = re.compile(r'• `([^`]+)`: (.*?)(?=\s+via |\n|$)')
PFX = re.compile(r'^(v3|v3r|v3h|v3p|v3o)-(.*?)(_t|_r|_b)?$')
NAMES = {'trainverify': 'TrainVerify', 'cvc5-logos': 'cvc5/logos', 'humanfia-icho2026': 'Humanfia IChO 2026',
         'formal-conjectures': 'formal-conjectures', 'longfellow-zk': 'longfellow-zk', 'asi-stack-book': 'asi-stack-book',
         'rs-mca': 'rs-mca (8 sub-projects)', 'sounio': 'sounio', 'lido-srv3': 'lido-srv3', 'berry-esseen': 'BerryEsseen',
         'strata': 'Strata', 'clean': 'clean', 'cedar-lean': 'cedar-spec', 'aks': 'aks',
         'sorting-network-expanders': 'sorting-network', 'aeneas-lean': 'aeneas'}
RS428 = ('rs-mca-RS_disproof_v3', 'rs-mca-cs25_cap_v13', 'rs-mca-moment_to_max', 'rs-mca-razorband_witness',
         'rs-mca-syndrome_line', 'rs-mca-syndrome_secant')
D_ORDER = ['v3', 'v3r', 'v3h', 'v3h_t', 'v3h_b', 'v3h_r']
COLS = ['D', 'G', 'P', 'O', 'K']   # v4: the order of the SPEC and of v2's Table 5 (general add-ons before options)


def read_rows(f):
    last = {}
    if not f.exists():
        return last
    for line in f.read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) < 6:
            continue
        c += [''] * (12 - len(c))
        last[(c[1], c[2])] = c
    return last


def pkg_of(base):
    return 'rs-mca' if base.startswith('rs-mca-') else base


def pass_loc(base, k):
    """(results stem, work dir, log suffix, harness time limit or 0) of pass k of base B, as in the pass runner's selection"""
    h = f'v3h-{base}'
    return {'v3': (f'v3-{base}', f'v3-{base}', '', 900), 'v3r': (f'v3r-{base}', f'v3r-{base}', '', 900),
            'v3h': (h, h, '', 0), 'v3h_t': (f'{h}_t', h, '_t', 3600), 'v3h_b': (f'{h}_b', h, '_b', 3600),
            'v3h_r': (f'{h}_r', h, '_r', 0)}[k]


# --- per-fact passes
passes = collections.defaultdict(dict)   # base -> {pass: {(mod, ax): row}}
_seen = {}
for f in sorted((f for d in RES_DIRS for f in d.glob('v3*.ax.tsv')), key=lambda p: p.name):
    if f.name in _seen:
        sys.exit(f'{f.name} found in more than one results folder')
    _seen[f.name] = f
    run = f.name[:-len('.ax.tsv')]
    m = PFX.match(run)
    if not m or run.startswith(('v3test', 'v3f-')):
        continue
    kind, base, suf = m.group(1), m.group(2), m.group(3) or ''
    if kind in ('v3', 'v3r', 'v3p', 'v3o') and suf:
        base, suf = base + suf, ''
    passes[base][kind + suf] = read_rows(f)

_idx = {}
if AXIDX is not None:
    _op = gzip.open if AXIDX.name.endswith('.gz') else open
    with _op(AXIDX, 'rt', errors='ignore') as fh:
        for l in fh:
            c = l.rstrip('\n').split('\t')
            if len(c) >= 4 and c[0] != 'base':
                _idx.setdefault(c[0], {})[(c[1], c[2])] = c[3]
def index_of(base):
    """axiom -> its index in its module, from the default run's module listings (one package build for every pass),
    or from the axiom index"""
    if base not in _idx:
        idx = {}
        if WORK is not None:
            for lf in (WORK / f'v3-{base}').glob('listax_*.log'):
                mod = lf.name[len('listax_'):-len('.log')]
                for l in lf.read_text(errors='ignore').splitlines():
                    c = l.split('\t')
                    if c[0] == 'AX' and len(c) >= 5:
                        idx[(mod, c[1])] = c[4]
        _idx[base] = idx
    return _idx[base]


def log_text(base, k, row):
    i = index_of(base).get((row[1], row[2]))
    if i is None:
        return None
    _, wd, suf, _ = pass_loc(base, k)
    safe = re.sub(r'[^A-Za-z0-9_]', '_', f"{row[1]}_{i}")[:150]
    name = f"ax{1 if row[4] == 'True' else 2}{suf}_{safe}.log"
    if WORK is not None:
        lg = WORK / wd / name
        return lg.read_text(errors='ignore') if lg.exists() else None
    for lg in (LOGS / wd / (name + '.gz'), LOGS / wd / name):
        if lg.exists():
            if lg.name.endswith('.gz'):
                with gzip.open(lg, 'rt', errors='ignore') as fh:
                    return fh.read()
            return lg.read_text(errors='ignore')
    return None


def harness(base, k, row, txt):
    if row[5] != 'ERROR':
        return False
    limit = pass_loc(base, k)[3]
    if not limit:
        return False
    if row[6] in ('rc143', 'rc-15'):
        return True
    if txt is None or 'out of memory' in txt or 'bad_alloc' in txt:
        return False
    m = re.findall(r'^rc=(-?\d+) secs=(\d+)', txt, re.M)
    return bool(m) and int(m[-1][0]) in (137, -9) and int(m[-1][1]) < limit - 5


facts = {}        # (base, mod, ax) -> dict(D=row, Dpass=k, conv={col: bool})
notbuilt = collections.Counter()
excluded = []
harness_left = []
for base, ps in passes.items():
    if 'v3' not in ps:
        continue
    keys = set()
    for k in D_ORDER:
        keys |= set(ps.get(k, {}))
    have_mod = {mk[0] for k in D_ORDER for mk, r in ps.get(k, {}).items() if r[5] != 'NOT_BUILT'}
    for key in sorted(keys):
        # converted if PROVED in any D pass (every driver run re-runs all phase-1 inner facts, so a fact proved in
        # v3 can get a later row from a run that did not select it); otherwise the verdict is the last row that is
        # not a harness failure, and a fact whose rows are all harness failures is listed in harness_D.tsv
        final, fk, ftxt, conv, last, lastk, lasttxt = None, None, None, False, None, None, None
        for k in D_ORDER:
            r = ps.get(k, {}).get(key)
            if r is None:
                continue
            if r[5] == 'PROVED':
                conv, final, fk, ftxt = True, r, k, None
                continue
            txt = log_text(base, k, r) if r[5] != 'NOT_BUILT' else None
            last, lastk, lasttxt = r, k, txt
            if not conv and not harness(base, k, r, txt):
                final, fk, ftxt = r, k, txt
        if final is None:
            final, fk, ftxt = last, lastk, lasttxt
        if final[5] == 'NOT_BUILT':
            if key[0] not in have_mod:
                notbuilt[base] += 1
            continue
        if (not base.startswith('s_') and final[5] == 'FAILED' and final[6] == 'other' and ftxt is not None
                and 'does not state an equation' in ftxt):
            excluded.append((base,) + key)      # corpus rule only (paper_numbers.py); the sample counts them
            continue
        if not conv and harness(base, fk, final, ftxt):
            harness_left.append((base, key[0], key[1], fk, final[6]))
        facts[(base,) + key] = {'D': final, 'Dpass': fk, 'conv': {'D': conv}, 'txt': ftxt}

# --- later columns (a fact converts in a column if PROVED in one of its files or in an earlier column)
colfiles = collections.defaultdict(list)    # (col, base) -> [stem]
for base, ps in passes.items():
    if 'v3p' in ps:
        colfiles[('P', base)].append(f'v3p-{base}')
    if 'v3o' in ps:
        colfiles[('O', base)].append(f'v3o-{base}')
missing = []
if MAP:
    for line in MAP.read_text().splitlines():
        if not line.strip() or line.startswith('#'):
            continue
        col, base, stem = line.split('\t')[:3]
        if col not in COLS[1:]:
            sys.exit(f'bad map line: {line!r}')
        if not find_res(f'{stem}.ax.tsv').exists():
            missing.append((col, base, stem))     # planned files: listed in map_used.tsv as missing
            continue
        colfiles[(col, base)].append(stem)
with outw('map_used.tsv') as fo:
    for col, base, stem in missing:
        fo.write(f"{col}\t{base}\t{stem}\tmissing\n")
    for (col, base), stems in sorted(colfiles.items()):
        for s in stems:
            rows = read_rows(find_res(f'{s}.ax.tsv'))
            hit = sum(1 for key, r in rows.items() if (base,) + key in facts and r[5] == 'PROVED')
            stray = sum(1 for key, r in rows.items() if (base,) + key not in facts and r[5] != 'NOT_BUILT')
            fo.write(f"{col}\t{base}\t{s}\trows={len(rows)}\tproved_known={hit}\tnot_in_D={stray}\n")
            for key, r in rows.items():
                fk = (base,) + key
                if fk in facts and r[5] == 'PROVED':
                    facts[fk]['conv'][col] = True
for v in facts.values():
    for i, col in enumerate(COLS):
        v['conv'][col] = v['conv'].get(col, False) or (i > 0 and v['conv'][COLS[i - 1]])

# --- rs-mca Lean 4.28: per theorem (m2_repo4.py)
pt = {}
for base in RS428:
    last = {}
    for kind in ('v3', 'v3r', 'v3h'):
        f = find_res(f"{kind}-{base}.tsv")
        if not f.exists():
            continue
        for line in f.read_text(errors='ignore').splitlines():
            c = line.split('\t')
            if len(c) >= 4:
                k = (c[1], c[2])
                prev = last.get(k)
                conv = (prev is not None and prev[1]) or c[3] == 'KERNELIZED'
                last[k] = (c, conv)
    for k, (c, conv) in last.items():
        if c[3] != 'NOT_BUILT':
            pt[(base,) + k] = (conv, c[3])

# --- per package
per = collections.defaultdict(collections.Counter)
verd = collections.defaultdict(collections.Counter)
for (base, mod, ax), v in facts.items():
    p = pkg_of(base)
    per[p]['facts'] += 1
    for col in COLS:
        per[p][col] += v['conv'][col]
    r = v['D']
    verd[p]['PROVED' if v['conv']['D'] else f"{r[5]} {r[6]}".strip()] += 1
for (base, mod, thm), (conv, last_v) in pt.items():
    per['rs-mca']['facts'] += 1
    for col in COLS:
        per['rs-mca'][col] += conv
    verd['rs-mca']['PROVED' if conv else f"theorem {last_v}"] += 1

# --- the study's verdict of each fact (the baseline): the study's result files, last row per (module, axiom); for the
# sample, sample_agg2.py's default overrides (two packages re-run with a patched tool, as the study reported them)
SAMPLE_OV = {'s_FrederickPu_Zag': 'retry-zag'}   # as the paper's study numbers (index row RS6)
def study_file(base):
    if base.startswith('s_'):
        if STUDY_S is None:
            return None
        ov = SAMPLE_OV.get(base)
        return STUDY_S / f'{ov}.ax.tsv' if ov and (STUDY_S / f'{ov}.ax.tsv').exists() else STUDY_S / f'{base}.ax.tsv'
    return STUDY_M2 / f'{base}.ax.tsv' if STUDY_M2 else None
regress = []
HAVE_STUDY = bool(STUDY_M2 or STUDY_S)
if HAVE_STUDY:
    st_cache = {}
    for (base, mod, ax), v in sorted(facts.items()):
        if base not in st_cache:
            f = study_file(base)
            st_cache[base] = read_rows(f) if f is not None else {}
        r = st_cache[base].get((mod, ax))
        s_conv = r is not None and r[5] == 'PROVED'
        v['study'] = (r[5], r[6]) if r is not None else ('', '')
        p = pkg_of(base)
        per[p]['study'] += s_conv
        if s_conv and not v['conv']['D']:
            per[p]['regress'] += 1
            regress.append((base, mod, ax, v['D'][5], v['D'][6], v['Dpass']))
        elif not s_conv and v['conv']['D']:
            per[p]['gain'] += 1
    if STUDY_PT:
        for base in RS428:
            last = {}
            f = STUDY_PT / f'{base}.tsv'
            for line in (f.read_text(errors='ignore').splitlines() if f.exists() else []):
                c = line.split('\t')
                if len(c) >= 4:
                    k = (c[1], c[2])
                    prev = last.get(k)
                    last[k] = (prev is not None and prev) or c[3] == 'KERNELIZED'
            for (b, mod, thm), (conv, last_v) in pt.items():
                if b != base:
                    continue
                s_conv = last.get((mod, thm), False)
                per['rs-mca']['study'] += s_conv
                if s_conv and not conv:
                    per['rs-mca']['regress'] += 1
                    regress.append((base, mod, thm, f'theorem {last_v}', '', 'per-theorem'))
                elif not s_conv and conv:
                    per['rs-mca']['gain'] += 1
corpus = [p for p in per if not p.startswith('s_')]
sample = [p for p in per if p.startswith('s_')]
lines = []
def report(title, pkgs):
    lines.append(f"== {title}")
    nf = sum(per[p]['facts'] for p in pkgs)
    lines.append("package\tfacts\t" + '\t'.join(COLS))
    big = sorted(pkgs, key=lambda p: -per[p]['facts'])
    for p in big:
        lines.append(f"{NAMES.get(p, p)}\t{per[p]['facts']}\t" + '\t'.join(str(per[p][c]) for c in COLS))
    for col in COLS:
        nc = sum(per[p][col] for p in pkgs)
        rates = [per[p][col] / per[p]['facts'] for p in pkgs if per[p]['facts']]
        r1 = [p for p in pkgs if p != big[0]]
        r3 = [p for p in pkgs if p not in big[:3]]
        def pooled(ps):
            a = sum(per[p][col] for p in ps); b = sum(per[p]['facts'] for p in ps)
            return f"{a}/{b} = {100 * a / b:.2f}%" if b else '-'
        lines.append(f"{col}: pooled {nc}/{nf} = {100 * nc / nf:.2f}%; without {big[0]} {pooled(r1)}; without the "
                     f"three largest ({', '.join(big[:3])}) {pooled(r3)}; per-package median "
                     f"{100 * statistics.median(rates):.2f}% mean {100 * statistics.mean(rates):.2f}%")
report('corpus', corpus)
if sample:
    report('random sample', sample)
lines.append(f"modules not built: {dict(notbuilt)}")
lines.append(f"left out (do not state an equation): {len(excluded)}")
lines.append(f"rs-mca per-theorem facts: {len(pt)} (KERNELIZED in D: {sum(c for c, _ in pt.values())})")
lines.append(f"harness failures left in the final D rows: {len(harness_left)} (by pass: "
             f"{dict(sorted(collections.Counter(h[3] for h in harness_left).items()))})")
lines.append(f"final D pass of the facts: {dict(sorted(collections.Counter(v['Dpass'] for v in facts.values()).items()))}")
lines.append(f"map files not there yet: {len(missing)}" + (f" ({', '.join(m[2] for m in missing)})" if missing else ''))
with outw('harness_D.tsv') as fo:
    fo.write("base\tmodule\taxiom\tpass\treason\n")
    for h in sorted(harness_left):
        fo.write('\t'.join(h) + '\n')
with outw('verdicts_D.tsv') as fo:
    fo.write("package\tverdict\tfacts\n")
    for p in sorted(verd, key=lambda p: -per[p]['facts']):
        for k, n in sorted(verd[p].items(), key=lambda kv: (-kv[1], kv[0])):
            fo.write(f"{p}\t{k}\t{n}\n")


# --- classes of the facts the default protocol (D) leaves
def blockers_of(txt):
    out = {}
    for b, k in BLOCKER_RE.findall(txt or ''):
        out.setdefault(b, k.strip())
    return out
def detail_of(r, txt):
    """what the check log says stopped the kernel (for FAILED rows whose reason is 'other' and for resource rows)"""
    t = txt or ''
    if r[5] == 'FAILED' and r[6] == 'other' and 'does not state an equation' in t:
        return 'does not state an equation'
    if 'out of memory' in t or 'bad_alloc' in t:
        return 'out of memory'
    if 'deep recursion detected' in t:
        return 'kernel deep recursion'
    if 'maximum recursion depth' in t:
        return 'maxRecDepth'
    if 'Stack overflow' in t or 'stack overflow' in t:
        return 'stack overflow'
    if 'declaration type mismatch' in t:
        return 'declaration type mismatch'
    if 'so the kernel ran out of resources' in t:
        return 'kernel ran out of resources'
    if 'deterministic timeout' in t:
        return 'deterministic timeout'
    return '' if txt is not None else 'no log'
cls = collections.Counter(); cls_pkg = collections.defaultdict(collections.Counter)
with outw('facts_not_converted_D.tsv') as fo:
    fo.write("base\tmodule\taxiom\tverdict\treason\tclass\tblockers\tpass\ttactic\tinner\tdetail\tsecs\tmaxrss_kb\n")
    for (base, mod, ax), v in sorted(facts.items()):
        if v['conv']['D']:
            continue
        r = v['D']
        bl = blockers_of(v['txt']) or ({b: '' for b in r[10].split(';')} if r[10] else {})
        cons = sorted({construct(b, k) for b, k in bl.items()})
        if r[6] == 'false_in_logic':
            key = 'false in the logic'
        elif r[5] == 'FAILED' and r[6] == 'blocked' and cons:
            key = ' + '.join(cons)
        elif r[5] in ('TIMEOUT', 'ERROR'):
            key = 'kernel resources' + (', blocker reachable: ' + ' + '.join(cons) if cons else ', no blocker reachable')
        else:
            key = f"{r[5]} {r[6]}" + (': ' + ' + '.join(cons) if cons else '')
        cls[key] += 1; cls_pkg[key][pkg_of(base)] += 1
        fo.write('\t'.join([base, mod, ax, r[5], r[6], key, ';'.join(sorted(bl)), v['Dpass'], r[3], r[4],
                            detail_of(r, v['txt']), r[9], r[8]]) + '\n')
with outw('classes_D.tsv') as fo:
    fo.write("class\tfacts\tpackages\n")
    for k, n in sorted(cls.items(), key=lambda kv: (-kv[1], kv[0])):
        fo.write(f"{k}\t{n}\t" + ', '.join(f"{p} {c}" for p, c in sorted(cls_pkg[k].items(), key=lambda kv: (-kv[1], kv[0])))
                 + '\n')

# --- fact lists against the study
if STUDY_M2 or STUDY_S:
    with outw('factlist_diff.tsv') as fo:
        fo.write("base\tv3_facts\tstudy_facts\tonly_v3\tonly_study\n")
        for base in sorted(passes):
            if base in RS428 or 'v3' not in passes[base]:
                continue
            sf = None
            for d in (STUDY_M2, STUDY_S):
                if d and (d / f"{base}.ax.tsv").exists():
                    sf = d / f"{base}.ax.tsv"
            if sf is None:
                fo.write(f"{base}\t-\t-\tno study file\t\n"); continue
            st = {k for k, r in read_rows(sf).items() if r[5] != 'NOT_BUILT'}
            v3k = {(m, a) for (b, m, a) in facts if b == base} | {(m, a) for (b, m, a) in excluded if b == base}
            fo.write(f"{base}\t{len(v3k)}\t{len(st)}\t{len(v3k - st)}\t{len(st - v3k)}\n")

# --- every fact with its D row (for the time and memory figures) and its columns
with outw('facts_D.tsv') as fo:
    fo.write("base\tmodule\taxiom\ttactic\tinner\tverdict\treason\tsecs\tmaxrss_kb\tkernel_ms\tpass\t" + '\t'.join(COLS) +
             "\tstudy_verdict\tstudy_reason\n")
    for (base, mod, ax), v in sorted(facts.items()):
        r = v['D']
        sv = v.get('study', ('', ''))
        fo.write('\t'.join([base, mod, ax, r[3], r[4], 'PROVED' if v['conv']['D'] else r[5], r[6], r[9], r[8], r[7],
                            v['Dpass']] + [str(int(v['conv'][c])) for c in COLS] + [sv[0], sv[1]]) + '\n')

with outw('per_package.tsv') as fo:
    fo.write("package\tfacts\tstudy\t" + '\t'.join(COLS) + "\tregressions\tgains\n")
    for p in sorted(per, key=lambda p: -per[p]['facts']):
        fo.write(f"{p}\t{per[p]['facts']}\t{per[p]['study'] if HAVE_STUDY else '-'}\t" +
                 '\t'.join(str(per[p][c]) for c in COLS) + f"\t{per[p]['regress']}\t{per[p]['gain']}\n")
if HAVE_STUDY:
    with outw('regress_D.tsv') as fo:
        fo.write("base\tmodule\taxiom\tD_verdict\tD_reason\tD_pass\n")
        for r in regress:
            fo.write('\t'.join(r) + '\n')
    for title, pkgs in (('corpus', corpus), ('random sample', sample)):
        if pkgs:
            lines.append(f"baseline ({title}): study {sum(per[p]['study'] for p in pkgs)}, D "
                         f"{sum(per[p]['D'] for p in pkgs)} of {sum(per[p]['facts'] for p in pkgs)}; converted in the "
                         f"study but not in D {sum(per[p]['regress'] for p in pkgs)} (" +
                         ', '.join(f"{p} {per[p]['regress']}" for p in sorted(pkgs) if per[p]['regress']) +
                         f"); converted in D but not in the study {sum(per[p]['gain'] for p in pkgs)}")
OUTPUTS['summary.txt'] = ['\n'.join(lines) + '\n']
if CHECK is not None:
    bad = 0
    for name in sorted(OUTPUTS):
        text = ''.join(OUTPUTS[name])
        ref = CHECK / name
        same = ref.exists() and ref.read_text() == text
        bad += not same
        print(f"{name}\t{'identical' if same else ('DIFFERENT' if ref.exists() else 'MISSING in ' + str(CHECK))}")
    print(f"{len(OUTPUTS)} outputs, {len(OUTPUTS) - bad} identical")
    sys.exit(1 if bad else 0)
OUT.mkdir(parents=True)
for name, parts in OUTPUTS.items():
    (OUT / name).write_text(''.join(parts))
print('\n'.join(lines))
