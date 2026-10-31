#!/usr/bin/env python3
"""bvs_v3.py: the bv_decide sweep of paper v3 (sweeps): the archived bvs add-on (study/addon_versions/bvs_ed02e2be,
built unchanged per toolchain in W/build_<tc>) with NativeTrust v15, on every bv_decide fact of the corpus and the
random sample, that is, the study's 213-fact sweep (study/results/bv_decide/sweep/final_per_fact.tsv) without
Radix's 17 facts (Lean v4.29.0-rc4; the archived bvs needs Lean 4.31 or later).

Run on the box as ntbuild with `python3 -I`, inside a systemd unit v3ms-*-sweeps (the unit's MemoryMax caps the
whole run; each process also has the study's limits).

  bvs_v3.py list [--jobs 2]
      `bvs5_list M` for every module of the study's list, one process per module; writes W/facts.tsv
      (pkg, module, idx, axiom) and W/facts_compare.txt (the v3 list against the study's: (module, axiom) pairs and
      indices).
  bvs_v3.py run RUN [--jobs 2] [--budget-gb 8] [--max-pred 8] [--only RE] [--timeout 900] [--vmem-gb 48]
      one process per fact running `bvs5_fact M i` (as the study's sweep: 900 s, 48 GiB address space, one thread,
      -j1, compiled with -o so that the olean keeps the theorems for the checks). Files
      W/facts/<pkg>/G_<module>_<i>.{lean,log,olean,progress}; results W/results/RUN.tsv, one row per fact (facts
      with a row are skipped, so a restart resumes). At most --jobs processes run, and their predicted peaks
      (the study's peak for the fact x 1.3 + 0.5 GB, or 48 GB for a fact that the study's sweep did not convert in
      this setting) sum to at most --budget-gb; facts predicted above --max-pred are left for a run with a larger
      slot.
  bvs_v3.py check RUN [--jobs 2]
      for every CONVERTED fact of RUN, a fresh process imports the fact's olean and the original module, prints the
      axioms of bvs5fact_<i>.unsat and of every rebuilt declaration bvs5_<k>, and compares the type of each bvs5_<k>
      with the type of its original (kernel terms), as the study's checks.py. Results W/checks/RUN.axioms.tsv.

Every check file imports NativeTrust (the v15 build of the package's toolchain that its v3 default run uses:
nt_fix14, else v3/nt_v15) and BVS. LEAN_PATH: NativeTrust, the bvs build, the package's own path
(`lake env printenv LEAN_PATH`, as the v3 driver computes it; cached in W/lp_<pkg>.txt), W/facts/<pkg>.
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import argparse, os, re, signal, subprocess, sys, time
from pathlib import Path

W = Path((NT_BOX + '/v3/sweeps/bvs'))
HOME = Path(NT_BOX)
ELAN = HOME / 'elan'
STUDY = W / 'study_final_per_fact.tsv'   # byte copy of study/results/bv_decide/sweep/final_per_fact.tsv
STD = ['propext', 'Classical.choice', 'Quot.sound']
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*$")
PKGS = {
    's_opencompl_veir': ((NT_BOX + '/repos_s/opencompl_veir'), 'v4.35.0-rc4'),
    's_Natuvea_tacenta_core_tacenta_model': ((NT_BOX + '/repos_s/Natuvea_tacenta-core/tacenta-model'), 'v4.31.0'),
    's_Natuvea_tacenta_core_tacenta_proofs': ((NT_BOX + '/repos_s/Natuvea_tacenta-core/tacenta-proofs'), 'v4.31.0'),
    'clean': ((NT_BOX + '/repos/clean'), 'v4.33.1'),
    'asi-stack-book': ((NT_BOX + '/repos/asi-stack-book/lean'), 'v4.31.0'),
}
COLS = ['run', 'pkg', 'module', 'idx', 'axiom', 'verdict', 'reason', 'wall_s', 'maxrss_kb', 'rc', 'unsat_kernel_ms',
        'unsat_wall_ms', 'stats', 'users', 'users_std_same', 'users_left', 'users_failed', 'fact_std', 'fact_axioms',
        'pred_gb', 'nt']


def esc(m):
    return '.'.join(c if IDENT_RE.match(c) else f'«{c}»' for c in m.split('.'))


def safe(s):
    return re.sub(r'[^A-Za-z0-9_]', '_', s)[:120]


def nt_root(tc):
    """NativeTrust v15 build of tc, as the package's v3 default run uses it: nt_fix14, else v3/nt_v15."""
    for r in (HOME / 'nt_fix14', HOME / 'v3' / 'nt_v15'):
        res = r / f'result_{tc}.txt'
        if res.exists() and res.read_text().startswith(f'{tc} OK') and (r / tc / '.lake/build/lib/lean/NativeTrust.olean').exists():
            return r / tc
    sys.exit(f'no NativeTrust v15 build for {tc}')


def pkg_env(name):
    d, tc = PKGS[name]
    have = (Path(d) / 'lean-toolchain').read_text().strip().split(':')[-1]
    if have != tc:
        sys.exit(f'{name}: toolchain {have}, expected {tc}')
    lpf = W / f'lp_{name}.txt'
    if not lpf.exists():
        e = dict(os.environ, ELAN_HOME=str(ELAN), PATH=f'{ELAN}/bin:' + os.environ.get('PATH', '/usr/bin:/bin'))
        p = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=d, env=e, capture_output=True, text=True,
                           timeout=600, stdin=subprocess.DEVNULL)
        if p.returncode != 0 or not p.stdout.strip():
            sys.exit(f'{name}: lake env failed rc={p.returncode} {p.stderr[:300]}')
        lpf.write_text(p.stdout.strip() + '\n')
    nt = nt_root(tc)
    L = ELAN / 'toolchains' / f'leanprover--lean4---{tc}'
    fd = W / 'facts' / name
    fd.mkdir(parents=True, exist_ok=True)
    (fd / 'sat').mkdir(exist_ok=True)
    e = dict(os.environ)
    e['LEAN_PATH'] = ':'.join([str(nt / '.lake/build/lib/lean'), str(W / f'build_{tc}' / '.lake/build/lib/lean'),
                               lpf.read_text().strip(), str(fd)])
    e['LEAN_NUM_THREADS'] = '1'
    e['PATH'] = f'{L}/bin:' + os.environ.get('PATH', '/usr/bin:/bin')
    return dict(name=name, dir=d, tc=tc, nt=str(nt), lean=str(L / 'bin' / 'lean'), env=e, fd=fd)


def study_facts():
    """[(pkg, module, idx, axiom, verdict, peak_gb)] of the study's sweep, Radix excluded."""
    out = []
    for l in STUDY.read_text().splitlines()[1:]:
        c = l.split('\t')
        if c[0] in PKGS:
            out.append((c[0], c[1], int(c[2]), c[3], c[15], float(c[19] or 0)))
    return out


def start(p, src, olean, log, timeout, vmem_kb):
    """lean on src in p's facts dir, in its own session; the limits of the study's sweep (box_run2.sh)."""
    out = ['-o', olean] if olean else []
    sh = (f'ulimit -n 65536 2>/dev/null || ulimit -n $(ulimit -Hn); ulimit -v {vmem_kb}; ulimit -s 4194304 2>/dev/null; '
          f'exec /usr/bin/time -f "BVS_TIME wall=%e user=%U maxrss_kb=%M" timeout -k 30 {timeout} "$@"')
    f = open(log, 'w')
    f.write(f'BVS_CMD tc={p["tc"]} nt={p["nt"]} file={src} start={time.strftime("%FT%TZ", time.gmtime())}\n')
    f.flush()
    pr = subprocess.Popen(['bash', '-c', sh, 'cap', p['lean'], '-j1', '--tstack=1048576'] + out + [src], cwd=p['fd'],
                          env=p['env'], stdout=f, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                          start_new_session=True)
    f.close()
    return pr


def session_pids(sid):
    """PIDs whose session id is sid: the processes of a session that start() created (start_new_session), that is
    our own children only (coreutils `timeout` makes a new process group, not a new session)."""
    out = []
    for e in os.listdir('/proc'):
        if e.isdigit():
            try:
                st = open(f'/proc/{e}/stat').read()
                if int(st[st.rindex(')') + 2:].split()[3]) == sid:
                    out.append(int(e))
            except (OSError, ValueError, IndexError):
                pass
    return out


def reap(pr, t0, timeout):
    """rc of a finished process; a session still alive 120 s past the limit is killed (its own PIDs only)."""
    rc = pr.poll()
    if rc is None and time.time() - t0 > timeout + 120:
        for pid in session_pids(pr.pid):
            try:
                os.kill(pid, signal.SIGKILL)
            except OSError:
                pass
        rc = pr.wait()
    return rc


def parse_log(txt):
    d = dict(unsat={}, fail={}, users=[], user_fail=[], user_skip=[], done=None, time={}, stats={})
    for l in txt.splitlines():
        c = l.split('\t')
        if c[0] == 'BVS_UNSAT':
            d['unsat'][c[2]] = c
        elif c[0] == 'BVS_UNSAT_FAIL':
            d['fail'][c[2]] = c
        elif c[0] == 'BVS_USER':
            d['users'].append(c)
        elif c[0] == 'BVS_USER_FAIL':
            d['user_fail'].append(c)
        elif c[0] == 'BVS_USER_SKIP':
            d['user_skip'].append(c)
        elif c[0] == 'BVS_DONE':
            d['done'] = c
        elif c[0] == 'BVS_STATS':
            d['stats'][c[2]] = ' '.join(c[3:])
        elif l.startswith('BVS_TIME'):
            d['time'] = dict(x.split('=', 1) for x in l.split()[1:] if '=' in x)
    return d


def classify(rc, txt, d, i, timeout, wall, vmem_kb):
    """The study's rules (bvs.py classify), for one fact; a kill below the address-space limit (the unit's memory
    cap) is a harness failure: ERROR killed."""
    u = d['unsat'].get(str(i))
    if u is not None and u[9] == 'true' and d['done'] is not None:
        users = d['users']
        left = [x for x in users if x[4] != 'same_type=true' or x[7] != 'conv_left=0']
        failed = d['user_fail'] + d['user_skip']
        nstd = sum(1 for x in users if x[4] == 'same_type=true' and x[5] == 'std=true')
        if not users and not failed:
            return 'CONVERTED', 'no users in the module (unused axiom)'
        if not left and not failed:
            return 'CONVERTED', '' if nstd == len(users) else f'{len(users) - nstd} of {len(users)} rebuilt users still use other native facts'
        return 'UNSAT_ONLY', f'users: {len(left)} keep the axiom, {len(failed)} failed'
    if rc == 124 or (rc in (137, -9) and wall >= timeout):
        return 'TIMEOUT', f'{timeout}s'
    if 'std::bad_alloc' in txt or 'out of memory' in txt:
        return 'MEMORY', f'{vmem_kb // 1048576}GiB'
    if d['fail']:
        msg = ' '.join(c[5] for c in d['fail'].values() if len(c) > 5)
        if 'deterministic timeout' in msg:
            return 'FAILED', 'heartbeats'
        if 'maximum recursion depth' in msg:
            return 'FAILED', 'maxRecDepth'
        if 'did not report UNSAT' in msg:
            return 'FAILED', 'sat_solver'
        return 'FAILED', msg[:80]
    if 'Stack overflow' in txt or 'stack overflow' in txt:
        return 'ERROR', 'stack'
    if 'maximum recursion depth' in txt:
        return 'ERROR', 'maxRecDepth'
    rss = int(d['time'].get('maxrss_kb', '0') or 0)
    if rc in (137, -9) and rss < 0.9 * vmem_kb:
        return 'ERROR', f'killed rc{rc} at {rss // 1048576} GiB (unit memory cap?)'
    if rc in (134, 137, -9, -6):
        return 'MEMORY', f'rc{rc}'
    return 'ERROR', f'rc{rc}'


def cmd_list(a):
    mods = sorted({(f[0], f[1]) for f in study_facts()})
    todo, running, envs = list(mods), [], {}
    while todo or running:
        while todo and len(running) < a.jobs:
            name, m = todo.pop(0)
            p = envs[name] if name in envs else envs.setdefault(name, pkg_env(name))
            src = f'L_{safe(m)}.lean'
            (p['fd'] / src).write_text(f'import NativeTrust\nimport BVS\nimport {esc(m)}\nbvs5_list {esc(m)}\n')
            log = p['fd'] / f'L_{safe(m)}.log'
            running.append((name, m, start(p, src, None, log, 1800, 50331648), time.time(), log))
        for r in list(running):
            rc = reap(r[2], r[3], 1800)
            if rc is not None:
                running.remove(r)
                print(f'list {r[0]} {r[1]} rc={rc}', flush=True)
        time.sleep(1)
    rows = []
    for name, m in mods:
        txt = (W / 'facts' / name / f'L_{safe(m)}.log').read_text(errors='ignore')
        for i, ax in re.findall(r'^(?:\S+:\d+:\d+: (?:info: )?)?(\d+): (\S+)\s*$', txt, re.M):
            rows.append((name, m, int(i), ax))
    (W / 'facts.tsv').write_text(''.join(f'{n}\t{m}\t{i}\t{ax}\n' for (n, m, i, ax) in rows))
    v3 = {(n, m, ax): i for (n, m, i, ax) in rows}
    st = {(f[0], f[1], f[3]): f[2] for f in study_facts()}
    rep = [f'v3 list: {len(v3)} facts in {len(mods)} modules; study list (Radix excluded): {len(st)}']
    rep.append(f'in both: {len(set(v3) & set(st))}; only v3: {len(set(v3) - set(st))}; only study: {len(set(st) - set(v3))}')
    rep.append(f'same index: {sum(1 for k in set(v3) & set(st) if v3[k] == st[k])}')
    rep += [f'only v3\t{k}' for k in sorted(set(v3) - set(st))] + [f'only study\t{k}' for k in sorted(set(st) - set(v3))]
    rep += [f'index differs\t{k}\tv3 {v3[k]}\tstudy {st[k]}' for k in sorted(set(v3) & set(st)) if v3[k] != st[k]]
    (W / 'facts_compare.txt').write_text('\n'.join(rep) + '\n')
    print('\n'.join(rep[:3]))


def cmd_run(a):
    vmem_kb = int(a.vmem_gb * 1048576)
    facts = [l.split('\t') for l in (W / 'facts.tsv').read_text().splitlines() if l]
    st = {(f[0], f[1], f[3]): f for f in study_facts()}
    jobs = []
    for name, m, i, ax in facts:
        s = st.get((name, m, ax))
        pred = min(48.0, round(1.3 * s[5] + 0.5, 1)) if s and s[4] == 'CONVERTED' else 48.0
        jobs.append(dict(pkg=name, mod=m, idx=int(i), ax=ax, pred=pred))
    if a.only:
        jobs = [j for j in jobs if re.search(a.only, f'{j["pkg"]}|{j["mod"]}|{j["idx"]}')]
    out = W / 'results' / f'{a.run}.tsv'
    out.parent.mkdir(exist_ok=True)
    done = set()
    if out.exists():
        for l in out.read_text(errors='ignore').splitlines():
            c = l.split('\t')
            if len(c) > 4:
                done.add((c[1], c[2], c[3]))
    else:
        out.write_text('\t'.join(COLS) + '\n')
    jobs = [j for j in jobs if (j['pkg'], j['mod'], str(j['idx'])) not in done and j['pred'] <= a.max_pred]
    jobs.sort(key=lambda j: (j['pred'], j['pkg'], j['mod'], j['idx']))
    logf = open(W / 'results' / f'{a.run}.driver.log', 'a')
    def note(s):
        logf.write(f'{time.strftime("%FT%TZ", time.gmtime())} {s}\n')
        logf.flush()
    note(f'start jobs={len(jobs)} max_jobs={a.jobs} budget={a.budget_gb} max_pred={a.max_pred} timeout={a.timeout} vmem_kb={vmem_kb} pid={os.getpid()}')
    envs, running, queue = {}, [], list(jobs)
    while queue or running:
        for r in list(running):
            rc = reap(r['proc'], r['t0'], a.timeout)
            if rc is None:
                continue
            running.remove(r)
            wall = time.time() - r['t0']
            j = r['job']
            txt = r['log'].read_text(errors='ignore')
            d = parse_log(txt)
            verdict, reason = classify(rc, txt, d, j['idx'], a.timeout, wall, vmem_kb)
            u = d['unsat'].get(str(j['idx']))
            users = d['users']
            row = [a.run, j['pkg'], j['mod'], str(j['idx']), j['ax'], verdict, reason, f'{wall:.0f}',
                   d['time'].get('maxrss_kb', ''), str(rc), u[6] if u else '', u[7] if u else '',
                   d['stats'].get(str(j['idx']), ''), str(len(users)),
                   str(sum(1 for x in users if x[4] == 'same_type=true' and x[5] == 'std=true')),
                   str(sum(1 for x in users if x[4] != 'same_type=true' or x[7] != 'conv_left=0')),
                   str(len(d['user_fail']) + len(d['user_skip'])), u[9] if u else '', u[10] if u and len(u) > 10 else '',
                   str(j['pred']), r['nt']]
            with open(out, 'a') as f:
                f.write('\t'.join(row) + '\n')
            note(f'end {j["pkg"]}|{j["mod"]}|{j["idx"]} rc={rc} wall={wall:.0f} verdict={verdict} {reason}')
        reserved = sum(r['job']['pred'] for r in running)
        while queue and len(running) < a.jobs and reserved + queue[0]['pred'] <= a.budget_gb:
            j = queue.pop(0)
            p = envs[j['pkg']] if j['pkg'] in envs else envs.setdefault(j['pkg'], pkg_env(j['pkg']))
            stem = f'G_{safe(j["mod"])}_{j["idx"]}'
            fd = p['fd']
            (fd / f'{stem}.lean').write_text(
                f'import NativeTrust\nimport BVS\nimport {esc(j["mod"])}\nset_option Elab.async false\n'
                f'set_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
                f'set_option bvs4.workdir "{fd / "sat"}"\nset_option bvs4.timeout 600\n'
                f'set_option bvs4.log "{fd / (stem + ".progress")}"\n'
                f'bvs5_fact {esc(j["mod"])} {j["idx"]}\n')
            ol = fd / f'{stem}.olean'
            if ol.exists():
                ol.unlink()
            log = fd / f'{stem}.log'
            running.append(dict(job=j, proc=start(p, f'{stem}.lean', ol.name, log, a.timeout, vmem_kb),
                                t0=time.time(), log=log, nt=p['nt']))
            reserved += j['pred']
            note(f'start {j["pkg"]}|{j["mod"]}|{j["idx"]} pred={j["pred"]} running={len(running)}')
        if not running and queue:
            note(f'stop: next job pred {queue[0]["pred"]} > budget {a.budget_gb}')
            break
        time.sleep(2)
    note('all done')


PARSE = ('def parse (s : String) : Lean.Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with '
         '| some k => Lean.Name.mkNum n k | none => Lean.Name.mkStr n c) Lean.Name.anonymous')


def cmd_check(a):
    last = {}
    for l in (W / 'results' / f'{a.run}.tsv').read_text(errors='ignore').splitlines()[1:]:
        c = l.split('\t')
        if len(c) > 6:
            last[(c[1], c[2], c[3])] = c
    todo = sorted(k for k, c in last.items() if c[5] == 'CONVERTED')
    out = W / 'checks' / f'{a.run}.axioms.tsv'
    out.parent.mkdir(exist_ok=True)
    envs, running, rows = {}, [], []
    while todo or running:
        while todo and len(running) < a.jobs:
            name, m, i = todo.pop(0)
            p = envs[name] if name in envs else envs.setdefault(name, pkg_env(name))
            stem = f'G_{safe(m)}_{i}'
            txt = (p['fd'] / f'{stem}.log').read_text(errors='ignore')
            d = parse_log(txt)
            facts = [d['unsat'][i][8]] if i in d['unsat'] else []
            us = [(x[1], x[2]) for x in d['users']]
            lines = [f'import {stem}', f'import {esc(m)}', 'open Lean in', PARSE]
            lines += [f'#print axioms {f}' for f in facts] + [f'#print axioms {n}' for (_, n) in us]
            lines += ['open Lean in', '#eval show MetaM Unit from do']
            lines += [f'  IO.println s!"TYPE\\t{n}\\t{{(← getConstInfo (parse "{n}")).type == (← getConstInfo (parse "{o}")).type}}"' for (o, n) in us]
            if not us:
                lines.append('  pure ()')
            src = f'C_{stem}.lean'
            (p['fd'] / src).write_text('\n'.join(lines) + '\n')
            log = p['fd'] / f'C_{stem}.log'
            running.append(((name, m, i), facts, us, start(p, src, None, log, 1800, 50331648), time.time(), log))
        for r in list(running):
            rc = reap(r[3], r[4], 1800)
            if rc is None:
                continue
            running.remove(r)
            (name, m, i), facts, us, _, _, log = r
            txt = log.read_text(errors='ignore')
            ax = {k: ' '.join(v.split()) for k, v in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", txt)}
            noax = set(re.findall(r"'([^']+)' does not depend on any axioms", txt))
            types = dict(re.findall(r'TYPE\t(\S+)\t(true|false)', txt))
            for f in facts:
                ok = f in noax or (f in ax and all(x.strip() in STD for x in ax[f].split(',')))
                rows.append([name, m, i, f, 'fact', ax.get(f, '' if f in noax else '?'), 'std' if ok else 'NONSTD', '-', str(rc)])
            for (o, n) in us:
                ok = n in noax or (n in ax and all(x.strip() in STD for x in ax[n].split(',')))
                rows.append([name, m, i, n, o, ax.get(n, '' if n in noax else '?'), 'std' if ok else 'other-facts', types.get(n, '?'), str(rc)])
        time.sleep(0.5)
    out.write_text(''.join('\t'.join(r) + '\n' for r in rows))
    fr = [r for r in rows if r[4] == 'fact']
    ur = [r for r in rows if r[4] != 'fact']
    print(f'facts {len(fr)}: std {sum(1 for r in fr if r[6] == "std")}; rebuilt declarations {len(ur)}: std '
          f'{sum(1 for r in ur if r[6] == "std")}, type identical {sum(1 for r in ur if r[7] == "true")}, '
          f'differs {sum(1 for r in ur if r[7] == "false")}, unknown {sum(1 for r in ur if r[7] == "?")}')


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    l = sp.add_parser('list'); l.add_argument('--jobs', type=int, default=2)
    r = sp.add_parser('run'); r.add_argument('run')
    r.add_argument('--jobs', type=int, default=2); r.add_argument('--budget-gb', type=float, default=8.0)
    r.add_argument('--max-pred', type=float, default=8.0); r.add_argument('--only', default='')
    r.add_argument('--timeout', type=int, default=900); r.add_argument('--vmem-gb', type=float, default=48.0)
    c = sp.add_parser('check'); c.add_argument('run'); c.add_argument('--jobs', type=int, default=2)
    a = ap.parse_args()
    if not re.match(r'^[a-z0-9]+$', getattr(a, 'run', 'x')):
        sys.exit('bad run name')
    {'list': cmd_list, 'run': cmd_run, 'check': cmd_check}[a.cmd](a)


if __name__ == '__main__':
    main()
