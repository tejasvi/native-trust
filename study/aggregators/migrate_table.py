#!/usr/bin/env python3
"""Summary table of `ntrust migrate` runs: reads WORK/*/summary.json (default $NT_BOX/migrate) and prints a
Markdown table plus the remaining-occurrence reasons per package.
usage: migrate_table.py [WORK_DIR] [--names a,b,c]"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import json, sys
from pathlib import Path

work = Path(sys.argv[1]) if len(sys.argv) > 1 and not sys.argv[1].startswith('--') else Path((NT_BOX + '/migrate'))
names = None
if '--names' in sys.argv:
    names = sys.argv[sys.argv.index('--names') + 1].split(',')
rows = []
for f in sorted(work.glob('*/summary.json')):
    s = json.loads(f.read_text())
    if names and s['name'] not in names:
        continue
    rows.append(s)
if names:
    rows.sort(key=lambda s: names.index(s['name']))


def short(r):
    import re
    if r.startswith('build: build of the module exceeded'):
        return 'module build over the round limit (' + re.sub(r'\D', '', r) + ' s)'
    if 'maximum number of heartbeats' in r:
        return 'over maxHeartbeats after the rewrite (opt-in --bump-heartbeats)'
    if r.startswith('build: ') and ('decide' in r and 'failed' in r):
        return 'decide +kernel failed in the build'
    if r.startswith('build: ') and 'deep recursion' in r:
        return 'kernel deep recursion in the build'
    if r.startswith('build: '):
        return 'build error: ' + r[7:60]
    m = re.match(r'(plain )?(FAILED|ERROR|TIMEOUT)/(\S+)(?: \((.*)\))?', r)
    if m:
        what = {'blocked': 'blocked', 'other': 'stuck (cast in a Decidable instance)', 'memory': 'out of memory',
                'heartbeats': 'heartbeats', 'maxRecDepth': 'max recursion depth'}.get(m.group(3), m.group(3))
        extra = f" at {m.group(4).split(';')[0]}" if m.group(4) and m.group(3) == 'blocked' else ''
        if m.group(2) == 'TIMEOUT':
            return f"kernel over the per-fact time limit {m.group(3)} (per-fact result)"
        return f"kernel {what}{extra} (per-fact result)"
    if r == 'module not built':
        return 'module not built in the original'
    return r


def t(x):
    return '-' if x is None else f'{x:.1f}' if isinstance(x, float) else str(x)


print('| package | toolchain | uses | replaced (with facts + examples) | remaining | facts converted | native axioms before → after | '
      'native-dependent decls before → after | rewritten decls still native | build ok | affected modules | '
      'wall s before → after | CPU s before → after |')
print('|' + '---|' * 13)
tot = dict(uses=0, rep=0, rem=0, ax0=0, ax1=0, d0=0, d1=0, facts=0)
for s in rows:
    rem = s['uses'] - s['replaced']
    t0, t1 = s.get('time0') or {}, s.get('time1') or {}
    if not s.get('census_complete', True):
        s['name'] += ' (census incomplete)'
    print(f"| {s['name']} | {s['toolchain']} | {s['uses']} | {s['replaced']} ({s['replaced_known']} + {s['replaced_unknown']}) | {rem} | "
          f"{s.get('replaced_facts', '-')} of {s['native_axioms_before']} | "
          f"{s['native_axioms_before']} → {s['native_axioms_after']} | {s['native_dependent_decls_before']} → "
          f"{s['native_dependent_decls_after']} | {s['rewritten_decls_still_native']} of {s['rewritten_decls']} | "
          f"{('yes' if s['default_build'].get('rc') == 0 else 'NO') if s['build_ok'] and s.get('default_build') else ('rewritten modules yes; full build pending' if s['build_ok'] else 'NO')} | {s['affected_modules']} | "
          f"{t(t0.get('wall'))} → {t(t1.get('wall'))} | {t(t0.get('cpu'))} → {t(t1.get('cpu'))} |")
    if s['name'].endswith('-bump'):
        continue  # a variant of another row (opt-in --bump-heartbeats): not added to the totals
    tot['uses'] += s['uses']; tot['rep'] += s['replaced']; tot['rem'] += rem; tot['facts'] += s.get('replaced_facts', 0)
    tot['ax0'] += s['native_axioms_before']; tot['ax1'] += s['native_axioms_after']
    tot['d0'] += s['native_dependent_decls_before']; tot['d1'] += s['native_dependent_decls_after']
print(f"| **total** (without -bump rows) | | {tot['uses']} | {tot['rep']} | {tot['rem']} | {tot['facts']} of {tot['ax0']} | {tot['ax0']} → {tot['ax1']} | {tot['d0']} → {tot['d1']} | | | | | |")
print()
for s in rows:
    agg = {}
    for r, n in s['remaining'].items():
        agg[short(r)] = agg.get(short(r), 0) + n
    print(f"**{s['name']}** remaining: " + '; '.join(f'{n} {r}' for r, n in sorted(agg.items(), key=lambda kv: -kv[1])))
    if s.get('still_native_why'):
        whys = {}
        for d, why in s['still_native_why'].items():
            whys[why] = whys.get(why, 0) + 1
        print(f"  rewritten declarations still native: " + '; '.join(f'{n}: {w}' for w, n in whys.items()))
