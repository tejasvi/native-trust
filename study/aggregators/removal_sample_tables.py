#!/usr/bin/env python3
"""removal_sample_tables.py (v8: facts that NativeTrust v8 converts only with propSplit (pass B of the resource re-runs,
v8rp-s_NAME) form their own migrate class; v7: label of unread modules = after a failed build; v6: switch causes counted per remaining native AXIOM (census after, matched to the
kernel-first fallback message at the same file:line:col); migrate causes include unmatched (macro-made) axioms; error
counts from pinning.json; v5: only the variants of the rows shown; no times when time0 rebuilt no module;
v4: rows from the reruns where present: s2_NAME (migrate with the v8-proved facts
plain-checked, tools/v8rplain_v1.py) > c2_NAME (census fix) > s_NAME; switch kf-c2-NAME > kf-NAME; audit reverts grouped;
v3: build failures split into axiom-pinning checks (runs/pinning.json)
and real failures, variant rows (mig/var-*/variant_summary.json); v2: census-incomplete switch rows count unbuilt modules as unchanged, no time
ratio when no module was rewritten, build-failure lists): tables of the random-sample removal runs. Run as ntbuild on the box.
Reads runs/mig/s_NAME/{summary,plan}.json (ntrust_migrate_ms1.py) and mig/kf-NAME/kf_summary.json
(kfswitch_v1.py) for the packages of runs/pkgs24.tsv; per-fact verdicts from results/ (study run, or
retry-zag for Zag, overridden by the v8 re-runs v8r-s_NAME where present; plain v8 runs msv8p-s_NAME).
Prints Markdown: migrate table (format of migrate/summary_table.md), remaining reasons, switch table, pooled and
per-package median rates, remaining causes by class.
usage: NT_BOX=study/results/removal_sample python3 -I -B study/aggregators/removal_sample_tables.py
(from the artifact's top directory; NT_BOX holds runs/ and results/)"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import json, re, statistics, sys
from pathlib import Path

W = Path((NT_BOX + '/runs'))
ROOT = W / 'mig'
RES = Path((NT_BOX + '/results'))
STUDY = {'FrederickPu_Zag': 'retry-zag'}
# short(): copied from migrate/migrate_table.py (same reason labels as migrate/summary_table.md)
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

pk = [l.rstrip('\n').split('\t') for l in open(W / 'pkgs24.tsv')]
PIN = json.loads((W / 'pinning.json').read_text()) if (W / 'pinning.json').exists() else {}


def pin_kind(key):
    v = PIN.get(key)
    return v['kind'] if v else None


def rows_of(name):
    out = {}
    f = RES / f'{name}.ax.tsv'
    if f.exists():
        for l in open(f, errors='ignore'):
            c = l.rstrip('\n').split('\t')
            if len(c) >= 7 and c[2] not in ('', '-'):
                out[c[2]] = c
    return out


def c_of(v):  # ops/sample_cls.py classes
    verdict, reason, bl = v[5], v[6], (v[10] if len(v) > 10 else '')
    if verdict in ('ERROR', 'TIMEOUT'):
        return 'resources'
    if reason == 'blocked':
        if 'idOpaque' in bl or 'extrinsicFix' in bl:
            return 'iterator strings'
        if 'Lean.' in bl or 'PersistentHashMap' in bl:
            return 'meta layer'
        if 'getNumBits' in bl or 'hash' in bl.lower():
            return 'HashMap/USize'
        if 'Float' in bl:
            return 'Float'
        if 'WellFounded.fix' in bl:
            return 'WF copies not bridged'
        return 'other blocked'
    if verdict == 'FAILED' and reason == 'other':
        return 'stuck (cast in a Decidable instance)'
    return verdict + ':' + reason


def t(x):
    return '-' if x is None else f'{x:.1f}' if isinstance(x, float) else str(x)


def kf_adjust(k):
    """switch rows: modules the census could not read after the switch (not built) count as unchanged: their
    axioms from the census before are added to the after counts"""
    d = ROOT / f"kf-{k['name']}"
    per = {}
    try:
        for x in json.loads((d / 'census_before.json').read_text())['ax']:
            per[x['module']] = per.get(x['module'], 0) + 1
    except OSError:
        pass
    for key in ('after', 'after_hb2'):
        st = k.get(key)
        if st and st.get('failed'):
            add = sum(per.get(m, 0) for m in st['failed'])
            st['total'] += add
            st['unread_modules'] = len(st['failed'])
            st['unread_axioms'] = add


def pct(a, b):
    return f'{100 * a / b:.1f}%' if b else '-'


def med(v):
    v = [x for x in v if x is not None]
    return statistics.median(v) if v else None


mig, kf, miss_m, miss_k = [], [], [], []
for name, path, tc, *_ in pk:
    sf = next((ROOT / f'{pre}{name}' / 'summary.json' for pre in ('s2_', 'c2_', 's_')
               if (ROOT / f'{pre}{name}' / 'summary.json').exists()), ROOT / f's_{name}' / 'summary.json')
    if sf.exists():
        s = json.loads(sf.read_text())
        s['_short'] = name
        s['_dir'] = sf.parent
        s['_tag'] = {'s2_': ' [s2]', 'c2_': ' [c2]'}.get(sf.parent.name[:3], '')
        mig.append(s)
    else:
        miss_m.append(name)
    kfs = next((ROOT / f'{pre}{name}' / 'kf_summary.json' for pre in ('kf-c2-', 'kf-')
                if (ROOT / f'{pre}{name}' / 'kf_summary.json').exists()), ROOT / f'kf-{name}' / 'kf_summary.json')
    if kfs.exists() and json.loads(kfs.read_text()).get('finished'):
        kf.append(json.loads(kfs.read_text()))
        kf_adjust(kf[-1])
    else:
        miss_k.append(name)

# ------------------------------------------------------------------ migrate table
P = print
P('# Removal on the random sample: `ntrust migrate` and the one-import switch (library v8)\n')
P('Rows marked [s2]: migrate re-run after the facts that library v8 newly proves (the resource re-runs, pass A) were plain-checked '
  'too; [c2]: re-run with the census fix (a package-defined root `Expr` made the census script ambiguous).\n')
P('Packages: the 24 random-sample packages with native facts that build, i.e. the 26 of the paper\'s section '
  '"A random sample of repositories" without the two sections of tejasvi_smale6_six_bodies_generic_v4 (the owner\'s '
  'own package, excluded). Every row: the same tool versions (the same tools), fresh copies, 8 build threads.\n')
P('## 1. `ntrust migrate` (native_decide -> decide +kernel in a copy)\n')
P('| package | toolchain | uses | replaced (with facts + examples) | remaining | facts converted | native axioms before → after | '
  'native-dependent decls before → after | rewritten decls still native | build ok | affected modules | '
  'wall s before → after | CPU s before → after |')
P('|' + '---|' * 13)
tot = dict(uses=0, rep=0, rem=0, ax0=0, ax1=0, d0=0, d1=0, facts=0)
for s in mig:
    rem = s['uses'] - s['replaced']
    t0, t1 = s.get('time0') or {}, s.get('time1') or {}
    nm_ = s['_short'] + s['_tag'] + ('' if s.get('census_complete', True) else ' (census incomplete)')
    ok = ('yes' if s['default_build'].get('rc') == 0 else 'NO') if s['build_ok'] and s.get('default_build') else (
        'rewritten modules yes; full build pending' if s['build_ok'] else 'NO')
    s['_ok'] = ok == 'yes'
    s['_pin'] = (not s['_ok']) and pin_kind(f"mig {s['_short']} default") == 'axiom-pinning check'
    if s['_pin']:
        ok = 'axiom-pinning check only'
    s['_timed'] = bool(s['affected_modules']) and t0.get('rc') == 0 and t1.get('rc') == 0 and bool(t0.get('n_built'))
    if not s['affected_modules'] or not t0.get('n_built'):
        t0, t1 = {'wall': 'n/a', 'cpu': 'n/a'}, {'wall': 'n/a', 'cpu': 'n/a'}
    P(f"| {nm_} | {s['toolchain']} | {s['uses']} | {s['replaced']} ({s['replaced_known']} + {s['replaced_unknown']}) | {rem} | "
      f"{s.get('replaced_facts', '-')} of {s['native_axioms_before']} | {s['native_axioms_before']} → {s['native_axioms_after']} | "
      f"{s['native_dependent_decls_before']} → {s['native_dependent_decls_after']} | {s['rewritten_decls_still_native']} of "
      f"{s['rewritten_decls']} | {ok} | {s['affected_modules']} | {t(t0.get('wall'))} → {t(t1.get('wall'))} | "
      f"{t(t0.get('cpu'))} → {t(t1.get('cpu'))} |")
    tot['uses'] += s['uses']; tot['rep'] += s['replaced']; tot['rem'] += rem; tot['facts'] += s.get('replaced_facts', 0)
    tot['ax0'] += s['native_axioms_before']; tot['ax1'] += s['native_axioms_after']
    tot['d0'] += s['native_dependent_decls_before']; tot['d1'] += s['native_dependent_decls_after']
P('| tejasvi_smale6_six_bodies_generic_v4 (sections3_5, sections6_9) | | | | | | | | | | | | excluded: the owner\'s own package |')
P(f"| **total** ({len(mig)} packages) | | {tot['uses']} | {tot['rep']} | {tot['rem']} | {tot['facts']} of {tot['ax0']} | "
  f"{tot['ax0']} → {tot['ax1']} | {tot['d0']} → {tot['d1']} | | | | | |")
if miss_m:
    P(f'\nNot finished yet: {", ".join(miss_m)}')
P()
for s in mig:
    agg = {}
    for r, n in s['remaining'].items():
        agg[short(r)] = agg.get(short(r), 0) + n
    P(f"**{s['_short']}** remaining: " + '; '.join(f'{n} {r}' for r, n in sorted(agg.items(), key=lambda kv: -kv[1])))
    if s.get('still_native_why'):
        whys = {}
        for v in s['still_native_why'].values():
            whys[v] = whys.get(v, 0) + 1
        P('  rewritten declarations still native: ' + '; '.join(f'{n}: {k}' for k, n in whys.items()))

# ------------------------------------------------------------------ switch table
P('\n## 2. One-import switch (`import NativeTrust.KernelFirst`, unmodified calls)\n')
P('Whole package = every module the original build built (the set the census and `ntrust migrate` use). The import '
  'goes into each native module of a copy, with NativeTrust as a path dependency; clean rebuilds of all those '
  'modules, original and switched interleaved (median of 3 when the original build takes < 120 s).\n')
P('| package | toolchain | modules | native modules | native axioms before → after (budget 2000) | after (20000) | '
  'build ok | wall s before → after | CPU s before → after | wall ratio | fallbacks at 2000 (reason: calls) |')
P('|' + '---|' * 11)
kt = dict(ax0=0, ax1=0, ax2=0)
for k in kf:
    b, a1 = k['before']['total'], k['after']['total']
    a2 = k['after_hb2']['total'] if k.get('after_hb2') else None
    ratio = (k['kf_wall_med'] / k['orig_wall_med']) if k.get('kf_wall_med') and k.get('orig_wall_med') else None
    k['_ratio'] = ratio
    kfail = [b['tag'] for b in k.get('builds', []) if re.fullmatch(r'kf_\d+', b['tag']) and b['rc'] != 0]
    k['_pin'] = bool(kfail) and k['orig_build_ok'] and all(pin_kind(f"kf {k['name']} {t_}") == 'axiom-pinning check' for t_ in kfail)
    k['_cpu_ratio'] = (k['kf_cpu_med'] / k['orig_cpu_med']) if k.get('kf_cpu_med') and k.get('orig_cpu_med') else None
    fb = '; '.join(f'{r}: {n}' for r, n in sorted(k.get('fallbacks', {}).items(), key=lambda kv: -kv[1])[:4])
    inc = f" (census: {k['after']['unread_modules']} modules unread, their {k['after']['unread_axioms']} counted as kept)" if k['after'].get('unread_modules') else ''
    P(f"| {k['name']}{inc} | {k['toolchain']} | {k['modules']} | {k['native_files']} | {b} → {a1} | {t(a2)} | "
      f"{'yes' if k['kf_build_ok'] and k['orig_build_ok'] else 'axiom-pinning check only' if k['_pin'] else 'NO'} | {t(k.get('orig_wall_med'))} → {t(k.get('kf_wall_med'))} | "
      f"{t(k.get('orig_cpu_med'))} → {t(k.get('kf_cpu_med'))} | {t(round(ratio, 2) if ratio else None)} | {fb} |")
    kt['ax0'] += b; kt['ax1'] += a1; kt['ax2'] += a2 if a2 is not None else a1
P(f"| **total** ({len(kf)} packages) | | | | {kt['ax0']} → {kt['ax1']} | {kt['ax2']} (20000 where run) | | | | | |")
if miss_k:
    P(f'\nNot finished yet: {", ".join(miss_k)}')

# ------------------------------------------------------------------ rates
P('\n## 3. Rates (pooled = sums over packages; median = per-package median)\n')
P('| rate | migrate pooled | migrate median | switch (2000) pooled | switch (2000) median | switch (20000 where needed) pooled | median |')
P('|---|---|---|---|---|---|---|')
m_rep = [s['replaced'] / s['uses'] for s in mig if s['uses']]
m_ax = [(s['native_axioms_before'] - s['native_axioms_after']) / s['native_axioms_before'] for s in mig if s['native_axioms_before']]
k_ax = [(k['before']['total'] - k['after']['total']) / k['before']['total'] for k in kf if k['before']['total']]
k_ax2 = [(k['before']['total'] - (k.get('after_hb2') or k['after'])['total']) / k['before']['total'] for k in kf if k['before']['total']]
P(f"| (a) uses replaced | {pct(tot['rep'], tot['uses'])} ({tot['rep']}/{tot['uses']}) | {pct(med(m_rep) or 0, 1)} | "
  f"n/a (no call is edited) | | | |")
P(f"| (b) native axioms removed | {pct(tot['ax0'] - tot['ax1'], tot['ax0'])} ({tot['ax0'] - tot['ax1']}/{tot['ax0']}) | "
  f"{pct(med(m_ax) or 0, 1)} | {pct(kt['ax0'] - kt['ax1'], kt['ax0'])} ({kt['ax0'] - kt['ax1']}/{kt['ax0']}) | "
  f"{pct(med(k_ax) or 0, 1)} | {pct(kt['ax0'] - kt['ax2'], kt['ax0'])} ({kt['ax0'] - kt['ax2']}/{kt['ax0']}) | {pct(med(k_ax2) or 0, 1)} |")
okm = sum(1 for s in mig if s['_ok'])
okk = sum(1 for k in kf if k['kf_build_ok'] and k['orig_build_ok'])
pinm = sum(1 for s in mig if s.get('_pin'))
pink = sum(1 for k in kf if k.get('_pin'))
P(f"| (c) builds OK | {okm}/{len(mig)} (+{pinm} failing only in axiom-pinning checks, {len(mig) - okm - pinm} real failures) | | "
  f"{okk}/{len(kf)} (+{pink} axiom-pinning only, {len(kf) - okk - pink} real failures) | | "
  f"{sum(1 for k in kf if k.get('kf_hb2_build_ok') is not False)}/{len(kf)} (of the 20000 builds run: "
  f"{sum(1 for k in kf if k.get('kf_hb2_build_ok') is False)} failed) | |")
tm = [s for s in mig if s['_timed'] and s['time0'].get('wall') and s['time1'].get('wall')]
sw0 = sum(s['time0']['wall'] for s in tm); sw1 = sum(s['time1']['wall'] for s in tm)
sc0 = sum(s['time0']['cpu'] for s in tm); sc1 = sum(s['time1']['cpu'] for s in tm)
m_r = [s['time1']['wall'] / s['time0']['wall'] for s in tm]
m_rc = [s['time1']['cpu'] / s['time0']['cpu'] for s in tm if s['time0']['cpu']]
kw0 = sum(k['orig_wall_med'] for k in kf if k.get('_ratio'))
kw1 = sum(k['kf_wall_med'] for k in kf if k.get('_ratio'))
kc0 = sum(k['orig_cpu_med'] for k in kf if k.get('_cpu_ratio'))
kc1 = sum(k['kf_cpu_med'] for k in kf if k.get('_cpu_ratio'))
P(f"| (d) build-time ratio, wall (after/before) | {t(round(sw1 / sw0, 2) if sw0 else None)} | {t(round(med(m_r), 2) if m_r else None)} | "
  f"{t(round(kw1 / kw0, 2) if kw0 else None)} | {t(round(med([k['_ratio'] for k in kf]), 2) if kf else None)} | | |")
P(f"| (d) build-time ratio, CPU | {t(round(sc1 / sc0, 2) if sc0 else None)} | {t(round(med(m_rc), 2) if m_rc else None)} | "
  f"{t(round(kc1 / kc0, 2) if kc0 else None)} | {t(round(med([k['_cpu_ratio'] for k in kf]), 2) if kf else None)} | | |")
P(f'\nMigrate times: clean rebuild of the affected modules (time0 → time1), over the {len(tm)} packages where some module '
  'was rewritten. Switch times: clean rebuild of all modules (medians).')
P('\n### Build failures (axiom-pinning check = every error comes from the project\'s own axiom-audit code; pinning.json)\n')
for s in mig:
    if not s['_ok']:
        e = (s.get('default_build') or {}).get('errors') or []
        P(f"- migrate {s['_short']} [{pin_kind(f'mig {s[chr(95) + chr(115) + chr(104) + chr(111) + chr(114) + chr(116)]} default') or 'build failure'}]: full build rc={(s.get('default_build') or {}).get('rc')}, {len(e)}+ errors; first: "
          f"`{e[0]['file']}:{e[0]['line']}`: {e[0]['msg'][:160]}" if e else f"- migrate {s['_short']}: build_ok={s['build_ok']}")
for k in kf:
    for b in k.get('builds', []):
        if b['rc'] != 0:
            e = b.get('errors') or []
            P(f"- switch {k['name']} build {b['tag']} [{pin_kind(f'kf {k[chr(110) + chr(97) + chr(109) + chr(101)]} {b[chr(116) + chr(97) + chr(103)]}') or 'build failure'}]: rc={b['rc']}, {len(e)}+ errors, failed modules {len(b.get('failed_mods') or [])}; "
              + (f"first: `{e[0]['file']}:{e[0]['line']}`: {e[0]['msg'][:160]}" if e else f"tail: {b.get('tail', '')[-200:]}"))

var = sorted(ROOT.glob('var-*/variant_summary.json'))
if var:
    P('\n### VARIANT builds (not main rows): audit modules and their in-package dependents left out of the targets\n')
    P('| package | mode | modules | audit modules left out | dependents left out | targets | rc | built | errors | wall s |')
    P('|---|---|---|---|---|---|---|---|---|---|')
    shown = {str(s['_dir']) for s in mig} | {str(ROOT / f"kf-c2-{k['name']}") if (ROOT / f"kf-c2-{k['name']}").exists() else str(ROOT / f"kf-{k['name']}") for k in kf}
    for f in var:
        v = json.loads(f.read_text())
        rd = str(ROOT / Path(v['row_dir']).name) if v.get('row_dir') else str(ROOT / (f"s_{v['name']}" if v['mode'] == 'mig' else f"kf-{v['name']}"))
        if rd not in shown:
            continue
        b = v.get('build') or {}
        P(f"| {v['name']} | {'migrate (patched)' if v['mode'] == 'mig' else 'switch (import)'} | {v.get('modules')} | "
          f"{v.get('audit_modules')} | {len(v.get('dependents_excluded') or [])} | {v.get('targets')} | {b.get('rc')} | "
          f"{b.get('n_built')} | {len(b.get('errors') or [])} | {t(b.get('wall'))} |")

# ------------------------------------------------------------------ causes
P('\n## 4. What remains, by class (native axioms)\n')
mc, mcp = {}, {}
for s in mig:
    name = s['_short']
    study = rows_of(STUDY.get(name, 's_' + name))
    study.update(rows_of('v8r-s_' + name))
    plain = rows_of('msv8p-s_' + name)
    plain.update(rows_of('msv8p2-s_' + name))
    passb = {k for k, v in rows_of('v8rp-s_' + name).items() if v[5] == 'PROVED'}
    pf = s['_dir'] / 'plan.json'
    if not pf.exists():
        continue
    for o in json.loads(pf.read_text())['occs']:
        if o['status'] == 'replaced' or not o.get('facts'):
            continue
        r = o.get('reason', '')
        for ax in o['facts']:
            if any(x in r for x in ('reaches no native_decide axiom', 'depends on native_decide axiom',
                                    'compiled-pin REFUSED', 'does not match generated message')):
                k = "project axiom-audit check expects the native axiom (use reverted)"
            elif r.startswith('build:') or r in ('module not built', 'inside a macro/syntax definition',
                                                'the original module does not build'):
                k = short(r)
            elif ax in plain and plain[ax][5] != 'PROVED':
                k = 'needs NativeTrust transforms (plain kernel: ' + c_of(plain[ax]) + ')'
            elif ax in passb:
                k = 'converted by NativeTrust v8 only with propSplit (not plain; pass B)'
            elif ax in study and study[ax][5] != 'PROVED':
                k = c_of(study[ax])
            elif ax in study:
                k = 'proved by NativeTrust v8 only with transforms or after the plain run'
            else:
                k = 'no per-fact result'
            mc[k] = mc.get(k, 0) + 1
            mcp.setdefault(k, {})[name] = mcp.setdefault(k, {}).get(name, 0) + 1
    att = sum(v.get(name, 0) for v in mcp.values())
    rest = s['native_axioms_after'] - att - (s.get('bv_decide_axioms_after') or 0)
    if rest > 0:
        k = 'not matched to a source occurrence (macro-made facts, e.g. audit-tool test fixtures)'
        mc[k] = mc.get(k, 0) + rest
        mcp.setdefault(k, {})[name] = rest
    if s.get('bv_decide_axioms_after'):
        mc['bv_decide (never rewritten)'] = mc.get('bv_decide (never rewritten)', 0) + s['bv_decide_axioms_after']
        mcp.setdefault('bv_decide (never rewritten)', {})[name] = s['bv_decide_axioms_after']
P(f'**migrate** ({sum(mc.values())} native axioms; table total after = {tot["ax1"]}):\n')
P('| class | axioms | top packages |\n|---|---:|---|')
for k, n in sorted(mc.items(), key=lambda kv: -kv[1]):
    top = ', '.join(f'{p} {c}' for p, c in sorted(mcp[k].items(), key=lambda kv: -kv[1])[:4])
    P(f'| {k} | {n} | {top} |')


def kcls_r(r):
    if r.startswith('blocked: reaches'):
        b = (re.findall(r'`([^`]+)`', r) or ['?'])[0]
        return kcls('blocked: ' + b)
    if 'did not finish within' in r:
        return 'budget (heartbeats)'
    if 'ran out of resources' in r:
        return 'resources'
    if 'does not reduce the decision procedure' in r:
        return 'not reduced to true'
    if r.startswith('well-founded recursion'):
        return 'well-founded recursion'
    return r[:60]


def kcls(r):
    if r.startswith('blocked: '):
        b = r[9:]
        fake = ['', '', '', '', '', 'FAILED', 'blocked', '', '', '', b]
        return 'blocked: ' + c_of(fake)
    return r.split(':')[0] if r.startswith(('resources', 'not reduced')) else r


FBL = re.compile(r'^info: (?:\./)*(\S+?\.lean):(\d+):(\d+): kernel-first: .*? used compiled evaluation: (.*)$')
for tag, ckey, lkey in (('switch, budget 2000', 'after', None), ('switch, budget 20000 (where 2000 left axioms)', 'after_hb2', 'kf_hb2')):
    kc, kcp = {}, {}
    for k in kf:
        st = k.get(ckey)
        if not st:
            continue
        kd = next((ROOT / f"{p}{k['name']}" for p in ('kf-c2-', 'kf-') if (ROOT / f"{p}{k['name']}" / 'kf_summary.json').exists()), None)
        logn = lkey or f"kf_{k.get('reps', 1)}"
        calls = {}
        try:
            for l in (kd / f'build_{logn}.log').read_text(errors='ignore').splitlines():
                m = FBL.match(l.strip())
                if m:
                    calls[(Path(m.group(1)).stem, int(m.group(2)), int(m.group(3)))] = kcls_r(m.group(4))
        except OSError:
            pass
        try:
            axs = json.loads((kd / f'census_{"after" if ckey == "after" else "after_hb2"}.json').read_text())['ax']
        except OSError:
            axs = []
        def add(c, n=1):
            kc[c] = kc.get(c, 0) + n
            kcp.setdefault(c, {})[k['name']] = kcp.setdefault(c, {}).get(k['name'], 0) + n
        for x in axs:
            r = (x.get('range') or '-').split(':')
            key = (x['module'].split('.')[-1].replace('«', '').replace('»', ''), int(r[0]), int(r[1])) if len(r) == 4 else None
            if x['tactic'] == 'bv_decide':
                add('bv_decide (not handled by KernelFirst)')
            elif key in calls:
                add(calls[key])
            else:
                add('no kernel-first fallback message at the call (e.g. macro-made or `decide (config := ...)`)')
        if st.get('unread_axioms'):
            add('module not rebuilt: its switched build failed (axiom pins; codegraff: Std import) - counted as kept', st['unread_axioms'])
    P(f'\n**{tag}** (remaining native axioms; class = reason of the fallback at the same file:line:col):\n')
    P('| class | axioms | top packages |\n|---|---:|---|')
    for c, n in sorted(kc.items(), key=lambda kv: -kv[1]):
        top = ', '.join(f'{p} {x}' for p, x in sorted(kcp[c].items(), key=lambda kv: -kv[1])[:4])
        P(f'| {c} | {n} | {top} |')
