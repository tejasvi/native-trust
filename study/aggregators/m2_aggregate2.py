#!/usr/bin/env python3
"""Aggregate M2 results (v2): verdicts per package, and the facts that were not kernelized classified by the
construct that blocks them, read from the check logs.

usage: m2_aggregate2.py RESULTS_DIR WORK_DIR [--tsv OUT.tsv]

RESULTS_DIR/NAME.tsv: one line per fact (the last line per (module, theorem) counts; re-runs append):
package, module, theorem, verdict, reason, kernel_ms, maxrss_kb, secs, blockers[, n_direct, n_all, tactics]
WORK_DIR/NAME/chk*_*.log: the check logs; the newest log naming a theorem gives its blockers and their kinds.
"""
import collections, re, statistics, sys
from pathlib import Path

# blocker -> construct (by name first, then by the kind printed by #kernel_blockers)
def construct(name: str, kind: str) -> str:
    if 'extrinsicFix' in name or 'idOpaque' in name or name.startswith('Std.Iter') or 'Shrink' in name:
        return 'iterators/String.Slice (Std.Shrink, extrinsicFix)'
    if name == 'mixHash' or 'hash' in name.lower():
        return 'hashing (C primitive)'
    if name.startswith('Float') or name.startswith('Float32'):
        return 'Float'
    if name.startswith('String.Internal') or name.startswith('String.') and 'C' in kind:
        return 'String (C primitive)'
    if name.startswith('ByteArray') or name.startswith('FloatArray'):
        return 'ByteArray (C primitive)'
    if name == 'System.Platform.getNumBits' or 'USize' in name:
        return 'USize/platform word size'
    if name.startswith('IO.') or name.startswith('EIO') or name.startswith('BaseIO') or 'IO.RealWorld' in name:
        return 'IO'
    if name == 'Lean.Loop.forIn' or '`partial`' in kind or 'partial' in kind:
        return 'partial function / while loop'
    if 'extern' in kind or 'C (' in kind:
        return 'other C primitive (extern)'
    if name == 'WellFounded.fix':
        return 'WellFounded.fix'
    if kind.startswith('axiom'):
        return 'axiom'
    if 'implemented by' in kind:
        return 'opaque, implemented_by'
    if 'opaque' in kind:
        return 'other opaque constant'
    return 'other'


BLOCKER_RE = re.compile(r'• `([^`]+)`: (.*?)(?=\s+via |\n|$)')
THM_RE = re.compile(r'^(KERNELIZED|REJECTED|CLEAN) `([^`]+)`', re.M)


def log_blockers(work: Path):
    """(package, theorem) -> {blocker: kind} from the newest check log naming the theorem."""
    out = {}
    for pkgdir in sorted(p for p in work.iterdir() if p.is_dir()):
        logs = sorted(pkgdir.glob('chk*_*.log'), key=lambda p: p.stat().st_mtime)
        for lg in logs:
            txt = lg.read_text(errors='ignore')
            m = THM_RE.search(txt)
            if not m:
                continue
            bl = {}
            for b, k in BLOCKER_RE.findall(txt):
                bl.setdefault(b, k.strip())
            out[(pkgdir.name, m.group(2))] = bl
    return out


def load(d: Path):
    last = {}
    for f in sorted(d.glob('*.tsv')):
        for line in f.read_text(errors='ignore').splitlines():
            c = line.split('\t')
            if len(c) < 4:
                continue
            c += [''] * (12 - len(c))
            r = dict(pkg=c[0], mod=c[1], thm=c[2], verdict=c[3], reason=c[4], kms=c[5], rss=c[6], secs=c[7],
                     blockers=c[8], nd=c[9], na=c[10], tactics=c[11])
            last[(r['pkg'], r['mod'], r['thm'])] = r
    rows = list(last.values())
    # a NOT_BUILT line is superseded by any later fact line of the same module
    have_mod = {(r['pkg'], r['mod']) for r in rows if r['verdict'] != 'NOT_BUILT'}
    return [r for r in rows if r['verdict'] != 'NOT_BUILT' or (r['pkg'], r['mod']) not in have_mod]


def pct(n, d):
    return f"{100 * n / d:.0f}%" if d else "-"


def main():
    res, work = Path(sys.argv[1]), Path(sys.argv[2])
    out_tsv = sys.argv[sys.argv.index('--tsv') + 1] if '--tsv' in sys.argv else None
    rows = load(res)
    lb = log_blockers(work)
    facts = [r for r in rows if r['verdict'] != 'NOT_BUILT']
    nb = [r for r in rows if r['verdict'] == 'NOT_BUILT']
    by_pkg = collections.defaultdict(list)
    for r in facts:
        by_pkg[r['pkg']].append(r)
    print(f"theorems with direct native facts: {len(facts)} in {len(by_pkg)} packages; modules not built: {len(nb)}\n")
    print("| package | theorems | KERNELIZED | REJECTED (blocked) | REJECTED (false in logic) | REJECTED (other) | TIMEOUT | ERROR | CLEAN |")
    print("|---|---:|---:|---:|---:|---:|---:|---:|---:|")
    tot = collections.Counter()
    for p in sorted(by_pkg):
        rs = by_pkg[p]
        c = collections.Counter()
        for r in rs:
            v = r['verdict']
            if v == 'REJECTED':
                v = 'REJ_blocked' if r['reason'] == 'blocked' else 'REJ_false' if r['reason'] == 'false_in_logic' else 'REJ_other'
            c[v] += 1
        tot.update(c)
        n = len(rs)
        print(f"| {p} | {n} | {c['KERNELIZED']} ({pct(c['KERNELIZED'], n)}) | {c['REJ_blocked']} | {c['REJ_false']} | "
              f"{c['REJ_other']} | {c['TIMEOUT']} | {c['ERROR']} | {c['CLEAN']} |")
    n = len(facts)
    print(f"| **all** | {n} | {tot['KERNELIZED']} ({pct(tot['KERNELIZED'], n)}) | {tot['REJ_blocked']} | {tot['REJ_false']} | "
          f"{tot['REJ_other']} | {tot['TIMEOUT']} | {tot['ERROR']} | {tot['CLEAN']} |\n")
    sr = sum(1 for r in facts if r['verdict'] == 'KERNELIZED' and r['reason'] == 'stmt_rebuilt')
    print(f"kernelized with the statement over rebuilt definitions (nested native facts): {sr}")
    # classification of the facts not kernelized
    cls = collections.Counter()
    cls_pkg = collections.defaultdict(collections.Counter)
    detail = []
    for r in facts:
        if r['verdict'] in ('KERNELIZED', 'CLEAN'):
            continue
        bl = lb.get((r['pkg'], r['thm']), {})
        if not bl and r['blockers']:
            bl = {b: '' for b in r['blockers'].split(';')}
        cons = sorted({construct(b, k) for b, k in bl.items()})
        if r['verdict'] == 'REJECTED' and r['reason'] == 'false_in_logic':
            key = 'false in the logic (compiled code and logic disagree)'
        elif cons:
            key = ' + '.join(cons)
        elif r['verdict'] == 'TIMEOUT' or r['reason'] in ('memory', 'resources'):
            key = 'kernel resources (no blocker reachable)'
        else:
            key = f"unclassified ({r['verdict']} {r['reason']})"
        cls[key] += 1
        cls_pkg[key][r['pkg']] += 1
        detail.append((r['pkg'], r['mod'], r['thm'], r['verdict'], r['reason'], key, ';'.join(sorted(bl))))
    print("\nfacts not kernelized, by blocking construct:")
    for k, v in cls.most_common():
        print(f"  {v:6d}  {k}   [{', '.join(f'{p}:{c}' for p, c in cls_pkg[k].most_common(6))}]")
    tac = collections.Counter()
    for r in facts:
        for t in filter(None, r['tactics'].split(',')):
            tac[t.split(':')[0]] += 1
    if tac:
        print("\ntactics of the direct facts (theorems with at least one):", dict(tac))
    ks = sorted(int(r['kms']) for r in facts if r['verdict'] == 'KERNELIZED' and r['kms'].isdigit())
    if ks:
        q = lambda p: ks[min(len(ks) - 1, int(p * len(ks)))]
        print(f"\nkernel time of kernelized theorems (ms): median {statistics.median(ks):.0f}, p90 {q(0.9)}, max {ks[-1]}, "
              f"total {sum(ks) / 3.6e6:.2f} CPU-h")
    rs = sorted(int(r['rss']) for r in facts if r['rss'].isdigit())
    if rs:
        print(f"peak memory per check process: median {statistics.median(rs) / 1048576:.1f} GB, max {rs[-1] / 1048576:.1f} GB")
    if nb:
        print("modules not built:", collections.Counter(r['pkg'] for r in nb).most_common())
    if out_tsv:
        with open(out_tsv, 'w') as f:
            f.write("package\tmodule\ttheorem\tverdict\treason\tconstruct\tblockers\n")
            for d in detail:
                f.write('\t'.join(d) + '\n')


if __name__ == '__main__':
    main()
