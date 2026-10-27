#!/usr/bin/env python3
"""tables_b4.py (v4: the worst ratio with raw seconds (2 decimals) for checking rounded claims; v3: + the v14 re-run with the defaults (mig/v14_<pkg>) as the first budgeted row, the
v13 defaults run (mig/p_) kept as the comparison; v2: adds the run with the shipped defaults, mig/p_<pkg> = --fact-budget 2000
--max-slowdown 2 --max-rounds 10 (tools/ntrust_migrate_ms4.py), as the first budgeted row, with its slowdown reverts): budgeted `ntrust migrate` (ms3 --fact-budget) vs the unbudgeted rows, on the 24
random-sample packages. Run as ntbuild on the box. Rows: unbudgeted = mig/s2_ > c2_ > s_ (the final table);
budget HB = mig/b<HB>_<pkg>. A failed full build is classified with tools/pinning_v4.py's classify (axiom-pinning
check vs build failure). Prints Markdown: the trade-off per budget (pooled and median removal, uses replaced,
build-time ratio, builds), then one table per budget with the per-package rows.
usage: tables_b4.py [BUDGETS, default 2000,20000,200] > budget_table.md
In this copy: NT_BOX=study/results/removal_sample python3 -I -B study/results/removal_sample/runs/tools/tables_b4.py
(from the artifact's top directory). The classification of a failed build reads the package's sources, which the
artifact does not hold; without them zcash's build, an axiom-pinning check, counts as a failure."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import importlib.util, json, statistics, sys
from pathlib import Path

W = Path((NT_BOX + '/runs'))
ROOT = W / 'mig'
spec = importlib.util.spec_from_file_location('pin', W / 'tools/pinning_v4.py')
pin = importlib.util.module_from_spec(spec)
spec.loader.exec_module(pin)
budgets = [int(x) for x in (sys.argv[1] if len(sys.argv) > 1 else '2000,20000,200').split(',')]
pk = [l.rstrip('\n').split('\t') for l in open(W / 'pkgs24.tsv')]


def row(d: Path, name, path):
    f = d / 'summary.json'
    if not f.exists():
        return None
    s = json.loads(f.read_text())
    t0, t1 = s.get('time0') or {}, s.get('time1') or {}
    timed = bool(s.get('affected_modules')) and t0.get('rc') == 0 and t1.get('rc') == 0 and bool(t0.get('n_built'))
    db = s.get('default_build') or {}
    ok = bool(s.get('build_ok')) and db.get('rc') == 0
    kind = 'yes' if ok else None
    if not ok:
        lg = d / 'build_default.log'
        kind = pin.classify(lg, Path(path))['kind'] if lg.exists() else 'build failure'
        kind = 'axiom-pinning check only' if kind == 'axiom-pinning check' else 'NO'
    return dict(name=name, slowmods=len(s.get('slowdown_reverted_modules') or []), uses=s['uses'], rep=s['replaced'], facts=s.get('replaced_facts', 0),
                ax0=s['native_axioms_before'], ax1=s['native_axioms_after'], kind=kind, timed=timed,
                w0=t0.get('wall'), w1=t1.get('wall'), c0=t0.get('cpu'), c1=t1.get('cpu'),
                audit=(s.get('audit') or {}).get('tags', {}), remaining=s.get('remaining', {}))


def fmt(x, nd=1):
    return '-' if x is None else (f'{x:.{nd}f}' if isinstance(x, float) else str(x))


def med(v):
    v = [x for x in v if x is not None]
    return statistics.median(v) if v else None


def summarize(rows):
    rows = [r for r in rows if r]
    u, rp = sum(r['uses'] for r in rows), sum(r['rep'] for r in rows)
    a0, a1 = sum(r['ax0'] for r in rows), sum(r['ax1'] for r in rows)
    tm = [r for r in rows if r['timed'] and r['w0']]
    sw0, sw1 = sum(r['w0'] for r in tm), sum(r['w1'] for r in tm)
    sc0, sc1 = sum(r['c0'] for r in tm), sum(r['c1'] for r in tm)
    return dict(n=len(rows), uses=f"{100 * rp / max(u, 1):.1f}% ({rp}/{u})",
                uses_med=f"{100 * (med([r['rep'] / r['uses'] for r in rows if r['uses']]) or 0):.1f}%",
                ax=f"{100 * (a0 - a1) / max(a0, 1):.1f}% ({a0 - a1}/{a0})",
                ax_med=f"{100 * (med([(r['ax0'] - r['ax1']) / r['ax0'] for r in rows if r['ax0']]) or 0):.1f}%",
                wall=fmt(sw1 / sw0, 2) if sw0 else '-', wall_med=fmt(med([r['w1'] / r['w0'] for r in tm]), 2),
                cpu=fmt(sc1 / sc0, 2) if sc0 else '-', cpu_med=fmt(med([r['c1'] / r['c0'] for r in tm if r['c0']]), 2),
                worst=max(((r['w1'] / r['w0'], r['name'], r['w0'], r['w1']) for r in tm), default=(None, '-', None, None)),
                over2=sum(1 for r in tm if r['w1'] / r['w0'] > 2 and r['w1'] - r['w0'] > 5),
                ok=sum(1 for r in rows if r['kind'] == 'yes'),
                pin=sum(1 for r in rows if r['kind'] == 'axiom-pinning check only'),
                bad=sum(1 for r in rows if r['kind'] == 'NO'), ntimed=len(tm))


un = {}
for name, path, tc, *_ in pk:
    d = next((ROOT / f'{p}{name}' for p in ('s2_', 'c2_', 's_') if (ROOT / f'{p}{name}' / 'summary.json').exists()), None)
    un[name] = row(d, name, path) if d else None
bud = {hb: {name: row(ROOT / f'b{hb}_{name}', name, path) for name, path, tc, *_ in pk} for hb in budgets}
pair = {name: row(ROOT / f'v14_{name}', name, path) for name, path, tc, *_ in pk}
pair13 = {name: row(ROOT / f'p_{name}', name, path) for name, path, tc, *_ in pk}
P = print
P('# Per-fact budget for `ntrust migrate`: trade-off on the 24 random-sample packages\n')
P('Unbudgeted = the final table (rows s2/c2/s). Budget HB = `--fact-budget HB` (thousands of heartbeats): a use is '
  'rewritten only if every fact behind it is REPLACEABLE in `#native_decide_audit` under HB; examples are tried in the '
  'build rounds within the same budget. Times: clean rebuilds of the affected modules (time0 → time1), packages where '
  'some module was rebuilt. "> 2×" = packages whose affected modules take more than twice as long (and 5 s more).\n')
P('| run | packages | uses replaced pooled | median | native axioms removed pooled | median | wall ratio pooled | '
  'median | CPU ratio pooled | median | worst wall ratio | packages > 2× slower | builds OK (+pinning only, failures) |')
P('|' + '---|' * 13)
for lab, rows in ([('no budget (earlier table)', list(un.values())),
                   ('**v14, defaults: budget 2000 + max-slowdown 2**', list(pair.values())),
                   ('v13, defaults (comparison)', list(pair13.values()))] +
                  [(f'budget {hb} only', list(bud[hb].values())) for hb in budgets]):
    s = summarize(rows)
    w = s['worst']
    P(f"| {lab} | {s['n']} | {s['uses']} | {s['uses_med']} | {s['ax']} | {s['ax_med']} | {s['wall']} | {s['wall_med']} | "
      f"{s['cpu']} | {s['cpu_med']} | {fmt(w[0], 2)} ({w[1]}, {fmt(w[2], 2)} → {fmt(w[3], 2)} s) | {s['over2']} of {s['ntimed']} | {s['ok']} (+{s['pin']}, {s['bad']}) |")
P('\nmax-slowdown reverts in the v14 defaults run: ' + ', '.join(f"{r['name']} {r['slowmods']} module(s)" for r in pair.values() if r and r['slowmods']))
for hb in ['pair'] + budgets:
    rowsd = pair if hb == 'pair' else bud[hb]
    P('\n## v14, defaults (budget 2000 + max-slowdown 2); in brackets: no budget\n' if hb == 'pair' else f'\n## v13, budget {hb} only\n')
    P('| package | uses replaced (facts) | native axioms before → after (unbudgeted after) | build ok | '
      'wall s before → after (unbudgeted after) | audit verdicts |')
    P('|---|---|---|---|---|---|')
    for name, *_ in pk:
        r, u = rowsd[name], un[name]
        if not r:
            P(f'| {name} | not run yet | | | | |')
            continue
        tags = ', '.join(f'{k} {v}' for k, v in sorted(r['audit'].items(), key=lambda kv: -kv[1]))
        uw = fmt(u['w1']) if u and u['timed'] else 'n/a'
        tw = f"{fmt(r['w0'])} → {fmt(r['w1'])}" if r['timed'] else 'n/a (no module rebuilt)'
        P(f"| {name} | {r['rep']} of {r['uses']} ({r['facts']}) | {r['ax0']} → {r['ax1']} ({u['ax1'] if u else '-'}) | "
          f"{r['kind']} | {tw} ({uw}) | {tags} |")
