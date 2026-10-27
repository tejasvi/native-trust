#!/usr/bin/env python3
"""Aggregate the per-axiom M2 results (m2_axioms.py): one native fact = one `native_decide`/`bv_decide` axiom.

usage: m2_aggregate_ax.py RESULTS_DIR WORK_DIR [--tsv OUT.tsv] [--md]

RESULTS_DIR/NAME.ax.tsv (the last line per (module, axiom) counts): package, module, axiom, tactic, inner, verdict
(PROVED|FAILED|TIMEOUT|ERROR|NOT_BUILT), reason, kernel_ms, maxrss_kb, secs, blockers, trace.
WORK_DIR/NAME/ax*_*.log: the newest log naming an axiom gives its blockers with their kinds.
"""
import collections, re, statistics, sys
from pathlib import Path

sys.path.insert(0, str(Path(__file__).resolve().parent))
from m2_aggregate2 import construct  # noqa: E402

BLOCKER_RE = re.compile(r'• `([^`]+)`: (.*?)(?=\s+via |\n|$)')
AX_RE = re.compile(r'^(?:PROVED|FAILED) `([^`]+)`', re.M)


def log_blockers(work: Path):
    out = {}
    if not work.is_dir():
        return out
    for pkgdir in sorted(p for p in work.iterdir() if p.is_dir()):
        for lg in sorted(pkgdir.glob('ax[12]_*.log'), key=lambda p: p.stat().st_mtime):
            txt = lg.read_text(errors='ignore')
            m = AX_RE.search(txt)
            # timed-out processes have no verdict line: the axiom is the one named by the static report
            name = m.group(1) if m else (re.search(r'^`([^`]*\._native\.[^`]*)`: (?:no blocker|blockers:)', txt, re.M) or [None, None])[1]
            if not name:
                continue
            bl = {}
            for b, k in BLOCKER_RE.findall(txt):
                bl.setdefault(b, k.strip())
            out[(pkgdir.name, name)] = bl
    return out


def load(d: Path):
    last = {}
    for f in sorted(d.glob('*.ax.tsv')):
        for line in f.read_text(errors='ignore').splitlines():
            c = line.split('\t')
            if len(c) < 6:
                continue
            c += [''] * (12 - len(c))
            r = dict(pkg=c[0], mod=c[1], ax=c[2], tac=c[3], inner=c[4], verdict=c[5], reason=c[6], kms=c[7],
                     rss=c[8], secs=c[9], blockers=c[10], trace=c[11])
            last[(r['pkg'], r['mod'], r['ax'])] = r
    rows = list(last.values())
    have_mod = {(r['pkg'], r['mod']) for r in rows if r['verdict'] != 'NOT_BUILT'}
    return [r for r in rows if r['verdict'] != 'NOT_BUILT' or (r['pkg'], r['mod']) not in have_mod]


def pct(n, d):
    return f"{100 * n / d:.0f}%" if d else "-"


def main():
    res, work = Path(sys.argv[1]), Path(sys.argv[2])
    out_tsv = sys.argv[sys.argv.index('--tsv') + 1] if '--tsv' in sys.argv else None
    rows = load(res)
    lb = log_blockers(work)
    # experiments on a package already in the study (NAME-remedy: extra @[kernel_fact] modules; NAME-fuel: the fuel
    # route for well-founded recursion) are reported apart
    EXP = ('-remedy', '-fuel')
    remedy = [r for r in rows if r['pkg'].endswith(EXP)]
    rows = [r for r in rows if not r['pkg'].endswith(EXP)]
    # axioms whose name contains `_native` but which `native_decide` did not make (user-declared axioms, e.g.
    # test fixtures of axiom checkers): not facts of the study
    notnat = []
    for r in rows:
        if r['verdict'] == 'FAILED' and r['reason'] == 'other':
            for lg in ((work / r['pkg']).glob('ax[12]_*.log') if work.is_dir() else []):
                t = lg.read_text(errors='ignore')
                if f"FAILED `{r['ax']}`" in t and 'does not state an equation' in t:
                    notnat.append(r)
                    break
    rows = [r for r in rows if r not in notnat]
    facts = [r for r in rows if r['verdict'] != 'NOT_BUILT']
    nb = [r for r in rows if r['verdict'] == 'NOT_BUILT']
    by_pkg = collections.defaultdict(list)
    for r in facts:
        by_pkg[r['pkg']].append(r)
    print(f"native facts (axioms): {len(facts)} in {len(by_pkg)} packages; modules not built: {len(nb)}\n")
    print("| package | facts | PROVED | FAILED blocked | FAILED false in logic | FAILED other | TIMEOUT | ERROR |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|")
    tot = collections.Counter()
    for p in sorted(by_pkg, key=lambda p: -len(by_pkg[p])):
        rs = by_pkg[p]
        c = collections.Counter()
        for r in rs:
            v = r['verdict']
            if v == 'FAILED':
                v = 'F_blocked' if r['reason'] == 'blocked' else 'F_false' if r['reason'] == 'false_in_logic' else 'F_other'
            c[v] += 1
        tot.update(c)
        n = len(rs)
        print(f"| {p} | {n} | {c['PROVED']} ({pct(c['PROVED'], n)}) | {c['F_blocked']} | {c['F_false']} | {c['F_other']} | "
              f"{c['TIMEOUT']} | {c['ERROR']} |")
    n = len(facts)
    print(f"| **all** | {n} | {tot['PROVED']} ({pct(tot['PROVED'], n)}) | {tot['F_blocked']} | {tot['F_false']} | {tot['F_other']} | "
          f"{tot['TIMEOUT']} | {tot['ERROR']} |\n")
    tac = collections.Counter((r['tac'], r['verdict']) for r in facts)
    print("by tactic:", {f"{t}/{v}": k for (t, v), k in sorted(tac.items())})
    inner = collections.Counter(r['verdict'] for r in facts if r['inner'] == 'True')
    print("facts inside definitions (inner):", dict(inner))
    cls = collections.Counter()
    cls_pkg = collections.defaultdict(collections.Counter)
    detail = []
    for r in facts:
        if r['verdict'] == 'PROVED':
            continue
        bl = lb.get((r['pkg'], r['ax']), {})
        if not bl and r['blockers']:
            bl = {b: '' for b in r['blockers'].split(';')}
        cons = sorted({construct(b, k) for b, k in bl.items()})
        if r['reason'] == 'false_in_logic':
            key = 'false in the logic'
        elif r['verdict'] == 'FAILED' and r['reason'] == 'blocked' and cons:
            key = ' + '.join(cons)
        elif r['verdict'] in ('TIMEOUT', 'ERROR') and not cons:
            key = 'kernel resources, no blocker reachable'
        elif r['verdict'] in ('TIMEOUT', 'ERROR'):
            key = 'kernel resources, blocker reachable: ' + ' + '.join(cons)
        else:
            key = f"{r['verdict']} {r['reason']}" + (': ' + ' + '.join(cons) if cons else '')
        cls[key] += 1
        cls_pkg[key][r['pkg']] += 1
        detail.append((r['pkg'], r['mod'], r['ax'], r['verdict'], r['reason'], key, ';'.join(sorted(bl))))
    print("\nfacts not proved, by blocking construct:")
    for k, v in cls.most_common():
        print(f"  {v:6d}  {k}   [{', '.join(f'{p}:{c}' for p, c in cls_pkg[k].most_common(5))}]")
    # unlock potential: blocked facts whose reachable blocking constructs all lie in one class (static estimate:
    # removing that class removes every reachable blocker; the evaluation may still exceed resources)
    single = collections.Counter()
    for d in detail:
        if d[3] == 'FAILED' and d[4] == 'blocked':
            cons = set(d[5].split(' + '))
            if len(cons) == 1:
                single[d[5]] += 1
    if single:
        print("\nblocked facts with a single blocking construct (what removing it would unlock, statically):")
        for k, v in single.most_common():
            print(f"  {v:6d}  {k}")
    secs = sorted(int(r['secs']) for r in facts if r['verdict'] == 'PROVED' and r['secs'].isdigit())
    if secs:
        q = lambda p: secs[min(len(secs) - 1, int(p * len(secs)))]
        print(f"\nwall time per proved fact (s, incl. import): median {statistics.median(secs):.0f}, p90 {q(0.9)}, max {secs[-1]}")
    rs = sorted(int(r['rss']) for r in facts if r['rss'].isdigit())
    if rs:
        print(f"peak memory per process: median {statistics.median(rs) / 1048576:.1f} GB, max {rs[-1] / 1048576:.1f} GB")
    if nb:
        print("modules not built:", collections.Counter(r['pkg'] for r in nb).most_common())
    if notnat:
        print("excluded, axioms named `…_native…` that do not state `e = true` (not made by native_decide):",
              collections.Counter(r['pkg'] for r in notnat).most_common())
    if remedy:
        print("\nexperiments on packages of the study (-remedy: extra @[kernel_fact] modules; -fuel: fuel route):")
        for p in sorted({r['pkg'] for r in remedy}):
            rs = [r for r in remedy if r['pkg'] == p and r['verdict'] != 'NOT_BUILT']
            c = collections.Counter(r['verdict'] for r in rs)
            base_name = p.rsplit('-', 1)[0]
            base = [r for r in facts if r['pkg'] == base_name]
            cb = collections.Counter(r['verdict'] for r in base)
            print(f"  {p}: PROVED {c['PROVED']}/{len(rs)} (base run: {cb['PROVED']}/{len(base)})")
    # rates per package and averaged over packages (the pooled rate is dominated by the largest package)
    rates = [(p, sum(1 for r in by_pkg[p] if r['verdict'] == 'PROVED') / len(by_pkg[p]), len(by_pkg[p]))
             for p in by_pkg if by_pkg[p]]
    if rates:
        mean = sum(x for _, x, _ in rates) / len(rates)
        med = statistics.median(x for _, x, _ in rates)
        big = max(rates, key=lambda t: t[2])
        rest = [r for r in facts if r['pkg'] != big[0]]
        print(f"\nconversion rate averaged over {len(rates)} packages: mean {100*mean:.1f}%, median {100*med:.1f}%; "
              f"pooled without the largest package ({big[0]}, {big[2]} facts): "
              f"{100*sum(1 for r in rest if r['verdict'] == 'PROVED')/max(1,len(rest)):.1f}% of {len(rest)}")
    if out_tsv:
        with open(out_tsv, 'w') as f:
            f.write("package\tmodule\taxiom\tverdict\treason\tconstruct\tblockers\n")
            for d in detail:
                f.write('\t'.join(d) + '\n')


if __name__ == '__main__':
    main()
