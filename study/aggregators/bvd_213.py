#!/usr/bin/env python3
"""All bv_decide facts of the corpus and the random sample: the per-fact sweep plus the last nine (Section 7).

usage: python3 -I -B study/aggregators/bvd_213.py   (from the artifact's top directory)

Reads study/results/bv_decide/sweep/final_per_fact.tsv (one line per fact: the bitmask LRAT checker and the bit-blaster
route, verdicts in columns lrat_verdict and bvs4_verdict) and study/results/bv_decide/final9.tsv (the nine facts the
sweep did not convert, converted by later runs: one line per fact, each value with the log that records it).
Checks that the nine are exactly the facts the sweep left (same module and axiom index), that every cited log is in
the artifact, and that each value of a final9 line occurs in the logs cited for it (clauses and hints, kernel
milliseconds (or its parts: a base check, a bit-blaster run, segments and chunks, the last two summed over their
per-item lines), peak KiB, the axiom list, nanoda's declaration count; for statement_identical true, the cited check
has TYPE_IDENTICAL lines and all of them end in true). Prints the totals per package and per mechanism.

Then the fresh-process checks of the sweep (study/results/bv_decide/sweep/checks/RUN.axioms.tsv, one line per
declaration: fact, declaration, original declaration or 'fact' for the proof of the fact itself, axioms, std or
other-facts, type identical, exit code; RUN is sweep2 for the bitmask checker, bvs4a and bvs4b for the bit-blaster
route). For each converted fact, in a run that converted it: the proof of the fact uses only the standard axioms and
each rebuilt declaration has the type of its original. A rebuilt declaration that uses several facts still depends on
the others in a per-fact run (other-facts). Such facts were converted together: all facts of a module
(study/results/bv_decide/logs7/logs/accept_*.log) or facts of several modules or packages in one module
(study/results/bv_decide/groups.tsv, logs in study/results/bv_decide/logs7/groups/). The acceptance checks of these
runs are searched for a TYPE_IDENTICAL line of each such declaration whose rebuilt copy has only standard axioms, and
the declarations without one are listed. Each line of groups.tsv is checked against its logs: the BVS_STATS and
BVS_UNSAT lines of the fact (clauses, hints, base and chunk milliseconds, kernel milliseconds, wall time), the process
peak, the axioms of every fact and rebuilt declaration of the group (their numbers as stated in the line), the
TYPE_IDENTICAL lines and nanoda's declaration count.
"""
import collections
import glob
import re
from pathlib import Path

SW = Path('study/results/bv_decide/sweep/final_per_fact.tsv')
F9 = Path('study/results/bv_decide/final9.tsv')
GR = Path('study/results/bv_decide/groups.tsv')
CK = Path('study/results/bv_decide/sweep/checks')
ACC_MODULE = 'study/results/bv_decide/logs7/logs/accept_*.log'
ACC_GROUP = 'study/results/bv_decide/logs7/groups/logs/accept_*.log'
STD = {'propext', 'Classical.choice', 'Quot.sound'}


def table(p):
    rows = [l.rstrip('\n').split('\t') for l in p.read_text().splitlines()]
    return [dict(zip(rows[0], r)) for r in rows[1:]]


sw = table(SW)
conv = [r for r in sw if 'CONVERTED' in (r['lrat_verdict'], r['bvs4_verdict'])]
left = {(r['module'], r['idx']): r for r in sw if r not in conv}
print(f"sweep: {len(sw)} facts; converted {len(conv)} (bitmask checker {sum(r['lrat_verdict'] == 'CONVERTED' for r in sw)}, "
      f"bit-blaster route {sum(r['bvs4_verdict'] == 'CONVERTED' for r in sw)}); not converted {len(left)}")
f9 = table(F9)
keys = {(r['module'], r['axiom_index']) for r in f9}
print(f"final9: {len(f9)} facts; same facts as the sweep left: {keys == set(left)}")


def files(cell):
    out, missing = [], []
    for p in re.findall(r'study/results/bv_decide/logs7/[^\s;,)]+', cell):
        hits = sorted(glob.glob(p))
        (out.extend(hits) if hits else missing.append(p))
    return out, missing


def text_of(fs):
    return ''.join(Path(f).read_text(errors='replace') for f in fs)


def kernel_ok(total, parts, text):
    """total occurs in the logs, or it is the sum of the listed parts, each recorded in the logs (a part that the
    logs record per chunk or per segment is the sum of those lines)."""
    if total in text:
        return True
    ps = [(n.strip(), int(v)) for n, v in re.findall(r'([a-z-]+) (\d+)', parts)]
    if sum(v for _, v in ps) != int(total):
        return False
    for name, v in ps:
        if name == 'base':
            ok = re.search(rf'base check {v} ms|base {v} ms', text) is not None
        elif name == 'bit-blaster':
            ok = re.search(rf'bit-blaster run \([^)]*\) {v} ms', text) is not None
        elif name == 'segments':
            ok = sum(int(x) for x in re.findall(r'segment \d+ \(\d+ leaves\) (\d+) ms', text)) == v
        elif name == 'chunks':
            ok = re.search(rf'chunks {v} ms', text) is not None or \
                sum(int(x) for x in re.findall(r'chunk \d+ (\d+) ms', text)) == v
        else:
            ok = False
        if not ok:
            return False
    return True


def same_type_ok(text):
    v = re.findall(r'^TYPE_IDENTICAL \S+ \S+ (\S+)$', text, re.M)
    return bool(v) and all(x == 'true' for x in v)


def axioms_of(text):
    """declaration -> set of axioms, from the #print axioms output in text"""
    axs = {n: {a.strip() for a in s.split(',') if a.strip()}
           for n, s in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", text)}
    axs.update({n: set() for n in re.findall(r"'([^']+)' does not depend on any axioms", text)})
    return axs


rows_ok = 0
for r in f9:
    row_ok = True
    for col, vals in [('src_clauses_hints', [r['clauses'], r['hints']]), ('src_kernel_ms', [r['kernel_ms']]),
                      ('src_wall_peak', [r['peak_KiB']]), ('src_axioms_identical', [r['axioms_fresh_process']]),
                      ('src_nanoda', [r['nanoda_decls']] if r['nanoda_decls'] not in ('-', '') else [])]:
        fs, missing = files(r[col])
        if missing:
            print(f"  {r['fact']}: missing cited log {missing}")
            row_ok = False
        text = text_of(fs)
        for v in vals:
            if col == 'src_kernel_ms' and kernel_ok(v, r['kernel_parts_ms'], text):
                continue
            if v not in text:
                print(f"  {r['fact']}: value {v} ({col}) not found in {fs}")
                row_ok = False
        if col == 'src_axioms_identical' and r['statement_identical'] == 'true' and not same_type_ok(text):
            print(f"  {r['fact']}: statement_identical true, but the cited check has no TYPE_IDENTICAL lines or one is not true")
            row_ok = False
    rows_ok += row_ok
print(f"final9: {rows_ok} of {len(f9)} rows have every value in their cited logs")
mech = collections.Counter(r['mechanism'].split(' (')[0] for r in f9)
print('final9 mechanisms: ' + ', '.join(f'{m} {n}' for m, n in mech.most_common()))
total = len(conv) + (len(f9) if keys == set(left) else 0)
pk = collections.Counter(r['pkg'] for r in sw)
print(f"converted in all: {total} of {len(sw)}; packages: " + ', '.join(f"{p} {n}" for p, n in pk.most_common()))

# fresh-process checks of the sweep's converted facts
ax = {}
for run in ('sweep2', 'bvs4a', 'bvs4b'):
    for l in (CK / f'{run}.axioms.tsv').read_text().splitlines():
        c = l.split('\t')
        ax.setdefault((run, c[0]), []).append(c)
fact_std, clean, pending, nrebuilt, bad = 0, 0, collections.defaultdict(set), 0, []
for r in conv:
    key = f"{r['pkg']}|{r['module']}|{r['idx']}"
    runs = (['sweep2'] if r['lrat_verdict'] == 'CONVERTED' else []) + \
        (['bvs4a', 'bvs4b'] if r['bvs4_verdict'] == 'CONVERTED' else [])
    good = []
    for cs in [ax[(x, key)] for x in runs if (x, key) in ax]:
        fact = [c for c in cs if c[2] == 'fact']
        users = [c for c in cs if c[2] != 'fact']
        if fact and all(c[4] == 'std' for c in fact) and all(c[5] == 'true' for c in users) and \
                all(c[6] == '0' for c in cs):
            good.append(users)
    if not good:
        bad.append(key)
        continue
    fact_std += 1
    best = min(good, key=lambda us: sum(c[4] != 'std' for c in us))
    nrebuilt += len(best)
    if all(c[4] == 'std' for c in best):
        clean += 1
    else:
        for c in best:
            if c[4] != 'std':
                pending[c[2]].add(key)
print(f"sweep checks: {fact_std} of {len(conv)} converted facts have a run with the fact's proof at the standard axioms "
      f"and every rebuilt declaration ({nrebuilt}) of the original type" + (f"; without: {bad}" if bad else ''))
print(f"sweep checks: every rebuilt declaration at the standard axioms in the per-fact run: {clean} facts")


def accepted(pattern):
    """original declaration -> acceptance log, for rebuilt copies with the original type and only standard axioms"""
    acc = {}
    for f in sorted(glob.glob(pattern)):
        t = Path(f).read_text(errors='replace')
        axs = axioms_of(t)
        for new, orig in re.findall(r'^TYPE_IDENTICAL (\S+) (\S+) true$', t, re.M):
            if new in axs and axs[new] <= STD:
                acc.setdefault(orig, Path(f).name)
    return acc


def facts_of(decls):
    return set().union(*(pending[d] for d in decls)) if decls else set()


acc_m, acc_g = accepted(ACC_MODULE), accepted(ACC_GROUP)
pfacts = facts_of(pending)
open_m = sorted(d for d in pending if d not in acc_m)
open_all = sorted(d for d in open_m if d not in acc_g)
together = pfacts - facts_of(open_all)
print(f"sweep checks: depending on further facts in the per-fact run: {len(pfacts)} facts, {len(pending)} declarations; "
      f"at the standard axioms with those facts converted together: {len(pending) - len(open_all)} declarations "
      f"({', '.join(sorted({acc_m.get(d) or acc_g[d] for d in pending if d not in open_all}))}), {len(together)} facts; "
      f"not converted together: {len(open_all)} declarations, {len(facts_of(open_all))} facts")
for d in open_all:
    print(f"  not converted together: {d} (facts {', '.join(sorted(pending[d]))})")

# groups.tsv: facts of several modules or packages converted together, in one module
gr = table(GR)
gkeys = {(r['module'], r['axiom_index']) for r in gr}
need = {tuple(k.split('|')[1:]) for k in facts_of(open_m)}
grows_ok = 0
for r in gr:
    errs = []
    fs = {col: files(r[col]) for col in ('src_clauses_hints', 'src_kernel_ms', 'src_wall_peak', 'src_axioms_identical',
                                         'src_nanoda')}
    for col, (_, missing) in fs.items():
        if missing:
            errs.append(f'missing cited log {missing} ({col})')
    m, i = re.escape(r['module']), re.escape(r['axiom_index'])
    st = re.search(rf'^BVS_STATS\t{m}\t{i}\t(.*)$', text_of(fs['src_clauses_hints'][0]), re.M)
    stats = dict(kv.split('=', 1) for kv in st.group(1).split('\t')) if st else {}
    if not st or stats.get('clauses') != r['clauses'] or stats.get('hints') != r['hints']:
        errs.append(f"clauses/hints {r['clauses']}/{r['hints']} not in a BVS_STATS line of the fact")
    elif r['kernel_parts_ms'] != f"base {stats.get('base_ms')} + chunks {stats.get('chunk_ms')}" or \
            int(stats['base_ms']) + int(stats['chunk_ms']) != int(r['kernel_ms']):
        errs.append(f"kernel parts {r['kernel_parts_ms']} differ from the BVS_STATS line")
    un = re.search(rf'^BVS_UNSAT\t{m}\t{i}\t(.*)$', text_of(fs['src_kernel_ms'][0]), re.M)
    u = un.group(1).split('\t') if un else []
    if len(u) < 8 or u[3] != r['kernel_ms'] or f'{int(u[4]) / 1000:.2f}' != r['wall_s'] or u[6] != 'true' or \
            {a.strip() for a in u[7].strip('[]').split(',')} - STD:
        errs.append('kernel ms, wall time or the fact\'s axioms differ from the BVS_UNSAT line')
    if f"maxrss={r['peak_KiB']} KB" not in text_of(fs['src_wall_peak'][0]):
        errs.append(f"peak {r['peak_KiB']} KiB not in a TIME line")
    t = text_of(fs['src_axioms_identical'][0])
    axs = axioms_of(t)
    nf = re.search(r'(\d+) group facts', r['axioms_fresh_process'])
    nd = re.search(r'(\d+) rebuilt declarations', r['axioms_fresh_process'])
    facts_ax = {n for n in axs if n.endswith('.unsat')}
    types = re.findall(r'^TYPE_IDENTICAL (\S+) \S+ (\S+)$', t, re.M)
    if not (nf and nd) or len(facts_ax) != int(nf.group(1)) or len(set(axs) - facts_ax) != int(nd.group(1)) or \
            any(a - STD for a in axs.values()):
        errs.append(f"axioms: {r['axioms_fresh_process']!r} not as in the cited check")
    if r['statement_identical'] == 'true' and (len({n for n, _ in types}) != int(nd.group(1) if nd else -1) or
                                               any(v != 'true' for _, v in types)):
        errs.append('statement_identical true, but the TYPE_IDENTICAL lines do not cover every rebuilt declaration as true')
    if f"Checked {r['nanoda_decls']} declarations with no typechecker errors" not in text_of(fs['src_nanoda'][0]):
        errs.append(f"nanoda count {r['nanoda_decls']} not in the cited log")
    for e in errs:
        print(f"  {r['fact']}: {e}")
    grows_ok += not errs
print(f"groups: {grows_ok} of {len(gr)} rows have every value in their cited logs; the same facts as those not converted "
      f"together with their module: {gkeys == need}")
f9_ok = sum(r['statement_identical'] == 'true' and set(re.findall(r'[\w.]+', r['axioms_fresh_process'])) <= STD
            for r in f9) if rows_ok == len(f9) else 0
g_ok = len(together & facts_of([d for d in open_m if d not in open_all])) if grows_ok == len(gr) and gkeys == need else 0
print(f"statement and standard axioms checked in a fresh process for every rebuilt declaration: "
      f"{clean + len(together) - len(facts_of(open_m) & together) + g_ok + f9_ok} of {total} facts (sweep per fact {clean}, "
      f"with their module {len(together) - len(facts_of(open_m) & together)}, in a group {g_ok}, final9 {f9_ok})")
