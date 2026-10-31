#!/usr/bin/env python3
"""bvs_v3_pass2.py: the follow-up runs of the v3 bv_decide sweep (sweeps), as in the study (final9.tsv, groups.tsv),
with the archived bvs add-on (W/build_<tc>) and NativeTrust v15. Run on the box as ntbuild with `python3 -I`, inside a
systemd unit v3ms-*-sweeps.

  bvs_v3_pass2.py shard NAME PKG MODULE IDX shards|split [--k 4] [--seg 30000] [--par 4] [--timeout 3600]
      the sharded conversion of one fact (bvs5_prep, k shards; or bvs6_prep, the split base check with segments of
      --seg gates, k shards), as the add-on's scripts/shard.sh does it: the prep file is compiled in W/shards/NAME
      (it writes the shard files and the final file there), then the shard files, --par at a time, then the final
      file; every process with the study's limits (48 GiB address space, one thread, -j1, --tstack 1 GiB) and
      --timeout. Then a fresh process prints the axioms of the fact theorem and the rebuilt declarations and compares
      their types with the originals'. Results: one row in W/results/pass2.tsv; logs W/shards/NAME/*.log.
  bvs_v3_pass2.py group NAME PKG ITEM... [--timeout 3600]
      `bvs5_group "M:i,j" ...` in one process (W/groups/NAME.lean, -o), then the same fresh-process check; one row
      in W/results/pass2.tsv.
Each prep/group file imports NativeTrust (the v15 build of the package's toolchain, as its v3 default run) and BVS.
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import argparse, os, re, signal, subprocess, sys, time
from pathlib import Path

W = Path((NT_BOX + '/v3/sweeps/bvs'))
HOME = Path(NT_BOX)
ELAN = HOME / 'elan'
STD = ['propext', 'Classical.choice', 'Quot.sound']
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*$")
PKGS = {
    's_opencompl_veir': ((NT_BOX + '/repos_s/opencompl_veir'), 'v4.35.0-rc4'),
    's_Natuvea_tacenta_core_tacenta_model': ((NT_BOX + '/repos_s/Natuvea_tacenta-core/tacenta-model'), 'v4.31.0'),
    's_Natuvea_tacenta_core_tacenta_proofs': ((NT_BOX + '/repos_s/Natuvea_tacenta-core/tacenta-proofs'), 'v4.31.0'),
    'clean': ((NT_BOX + '/repos/clean'), 'v4.33.1'),
    'asi-stack-book': ((NT_BOX + '/repos/asi-stack-book/lean'), 'v4.31.0'),
}
VMEM_KB = 50331648
OPTS = 'set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n'
PARSE = ('def parse (s : String) : Lean.Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with '
         '| some k => Lean.Name.mkNum n k | none => Lean.Name.mkStr n c) Lean.Name.anonymous')


def esc(m):
    return '.'.join(c if IDENT_RE.match(c) else f'«{c}»' for c in m.split('.'))


def nt_root(tc):
    for r in (HOME / 'nt_fix14', HOME / 'v3' / 'nt_v15'):
        res = r / f'result_{tc}.txt'
        if res.exists() and res.read_text().startswith(f'{tc} OK') and (r / tc / '.lake/build/lib/lean/NativeTrust.olean').exists():
            return r / tc
    sys.exit(f'no NativeTrust v15 build for {tc}')


def pkg_env(name, wd):
    d, tc = PKGS[name]
    if (Path(d) / 'lean-toolchain').read_text().strip().split(':')[-1] != tc:
        sys.exit(f'{name}: toolchain differs from {tc}')
    lpf = W / f'lp_{name}.txt'   # written by bvs_v3.py (lake env printenv LEAN_PATH)
    if not lpf.exists():
        sys.exit(f'no {lpf}: run bvs_v3.py first')
    nt = nt_root(tc)
    L = ELAN / 'toolchains' / f'leanprover--lean4---{tc}'
    e = dict(os.environ)
    e['LEAN_PATH'] = ':'.join([str(wd), str(nt / '.lake/build/lib/lean'), str(W / f'build_{tc}' / '.lake/build/lib/lean'),
                               lpf.read_text().strip()])
    e['LEAN_NUM_THREADS'] = '1'
    e['PATH'] = f'{L}/bin:' + os.environ.get('PATH', '/usr/bin:/bin')
    return dict(tc=tc, nt=str(nt), lean=str(L / 'bin' / 'lean'), env=e)


def session_pids(sid):
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


def start(p, wd, src, olean, log, timeout):
    out = ['-o', olean] if olean else []
    sh = (f'ulimit -n 65536 2>/dev/null || ulimit -n $(ulimit -Hn); ulimit -v {VMEM_KB}; ulimit -s 4194304 2>/dev/null; '
          f'exec /usr/bin/time -f "BVS_TIME wall=%e user=%U maxrss_kb=%M" timeout -k 30 {timeout} "$@"')
    f = open(log, 'w')
    f.write(f'BVS_CMD tc={p["tc"]} nt={p["nt"]} file={src} start={time.strftime("%FT%TZ", time.gmtime())}\n')
    f.flush()
    pr = subprocess.Popen(['bash', '-c', sh, 'cap', p['lean'], '-j1', '--tstack=1048576'] + out + [src], cwd=wd,
                          env=p['env'], stdout=f, stderr=subprocess.STDOUT, stdin=subprocess.DEVNULL,
                          start_new_session=True)
    f.close()
    return pr


def wait_all(procs, timeout):
    """procs: list of (key, Popen, t0); returns {key: rc}; a session alive 120 s past the limit is killed (own PIDs)."""
    rcs = {}
    while len(rcs) < len(procs):
        for k, pr, t0 in procs:
            if k in rcs:
                continue
            rc = pr.poll()
            if rc is None and time.time() - t0 > timeout + 120:
                for pid in session_pids(pr.pid):
                    try:
                        os.kill(pid, signal.SIGKILL)
                    except OSError:
                        pass
                rc = pr.wait()
            if rc is not None:
                rcs[k] = rc
        time.sleep(1)
    return rcs


def run1(p, wd, src, olean, log, timeout):
    t0 = time.time()
    rc = wait_all([(0, start(p, wd, src, olean, log, timeout), t0)], timeout)[0]
    return rc, time.time() - t0, peak(log)


def peak(log):
    m = re.search(r'BVS_TIME wall=\S+ user=\S+ maxrss_kb=(\d+)', log.read_text(errors='ignore'))
    return int(m.group(1)) if m else 0


def check(p, wd, name, mods, log_txt, timeout=1800):
    """Fresh process: axioms of the fact theorems and rebuilt declarations, types against the originals."""
    facts = [c.split('\t')[8] for c in log_txt.splitlines() if c.startswith('BVS_UNSAT\t') and c.split('\t')[9] == 'true']
    us = [(c.split('\t')[1], c.split('\t')[2]) for c in log_txt.splitlines() if c.startswith('BVS_USER\t')]
    lines = [f'import {name}'] + [f'import {esc(m)}' for m in mods] + ['open Lean in', PARSE]
    lines += [f'#print axioms {f}' for f in facts] + [f'#print axioms {n}' for (_, n) in us]
    lines += ['open Lean in', '#eval show MetaM Unit from do']
    lines += [f'  IO.println s!"TYPE\\t{n}\\t{{(← getConstInfo (parse "{n}")).type == (← getConstInfo (parse "{o}")).type}}"' for (o, n) in us]
    if not us:
        lines.append('  pure ()')
    (wd / f'C_{name}.lean').write_text('\n'.join(lines) + '\n')
    rc, wall, pk = run1(p, wd, f'C_{name}.lean', None, wd / f'C_{name}.log', timeout)
    txt = (wd / f'C_{name}.log').read_text(errors='ignore')
    ax = {k: ' '.join(v.split()) for k, v in re.findall(r"'([^']+)' depends on axioms: \[([^\]]*)\]", txt)}
    noax = set(re.findall(r"'([^']+)' does not depend on any axioms", txt))
    types = dict(re.findall(r'TYPE\t(\S+)\t(true|false)', txt))
    ok = lambda n: n in noax or (n in ax and all(x.strip() in STD for x in ax[n].split(',')))
    return dict(rc=rc, facts=len(facts), facts_std=sum(1 for f in facts if ok(f)), users=len(us),
                users_std=sum(1 for (_, n) in us if ok(n)), types_same=sum(1 for (_, n) in us if types.get(n) == 'true'))


def row(cols):
    out = W / 'results' / 'pass2.tsv'
    out.parent.mkdir(exist_ok=True)
    if not out.exists():
        out.write_text('name\tpkg\twhat\tverdict\tsteps\tunsat_lines\tdone_line\tcheck\tnt\n')
    with open(out, 'a') as f:
        f.write('\t'.join(cols) + '\n')


def cmd_shard(a):
    wd = W / 'shards' / a.name
    if wd.exists():
        sys.exit(f'refused: {wd} exists')
    wd.mkdir(parents=True)
    (wd / 'sat').mkdir()
    p = pkg_env(a.pkg, wd)
    P = f'P_{a.name}'
    cmdline = (f'bvs5_prep {esc(a.module)} "." {a.k} {a.idx}' if a.mode == 'shards'
               else f'bvs6_prep {esc(a.module)} "." {a.k} {a.seg} {a.idx}')
    (wd / f'{P}.lean').write_text(f'import NativeTrust\nimport BVS\nimport {esc(a.module)}\n{OPTS}'
                                  f'set_option bvs4.workdir "{wd / "sat"}"\nset_option bvs4.timeout 600\n'
                                  f'set_option bvs4.log "{wd / (P + ".progress")}"\n{cmdline}\n')
    steps = []
    rc, wall, pk = run1(p, wd, f'{P}.lean', f'{P}.olean', wd / f'{P}.log', a.timeout)
    steps.append(f'prep rc={rc} wall={wall:.0f} peak_kb={pk}')
    verdict = 'FAILED'
    unsat, done, chk = '', '', ''
    shards = sorted(wd.glob(f'{P}_S*.lean'))
    if rc == 0 and shards and (wd / f'{P}_Final.lean').exists():
        t0 = time.time()
        todo, running, rcs, pks = list(shards), [], {}, {}
        while todo or running:
            while todo and len(running) < a.par:
                s = todo.pop(0)
                running.append((s.stem, start(p, wd, s.name, f'{s.stem}.olean', wd / f'{s.stem}.log', a.timeout), time.time()))
            r = running.pop(0)
            rcs.update(wait_all([r], a.timeout))
            pks[r[0]] = peak(wd / f'{r[0]}.log')
        steps.append(f'shards n={len(shards)} wall={time.time() - t0:.0f} rcs={sorted(set(rcs.values()))} max_peak_kb={max(pks.values())}')
        if all(v == 0 for v in rcs.values()):
            rc, wall, pk = run1(p, wd, f'{P}_Final.lean', f'{P}_Final.olean', wd / f'{P}_Final.log', a.timeout)
            steps.append(f'final rc={rc} wall={wall:.0f} peak_kb={pk}')
            txt = (wd / f'{P}_Final.log').read_text(errors='ignore')
            unsat = ' | '.join(l for l in txt.splitlines() if l.startswith('BVS_UNSAT'))[:600]
            done = ' | '.join(l for l in txt.splitlines() if l.startswith('BVS_DONE'))[:300]
            if rc == 0 and f'\t{a.idx}\t' in unsat and '\ttrue\t' in unsat:
                c = check(p, wd, f'{P}_Final', [a.module], txt)
                chk = ' '.join(f'{k}={v}' for k, v in c.items())
                verdict = 'CONVERTED' if c['rc'] == 0 and c['facts'] == c['facts_std'] == 1 and c['users'] == c['users_std'] == c['types_same'] else 'CHECK_FAILED'
    row([a.name, a.pkg, f'{a.mode} {a.module} {a.idx} k={a.k}' + (f' seg={a.seg}' if a.mode == 'split' else ''), verdict,
         '; '.join(steps), unsat, done, chk, p['nt']])
    print(a.name, verdict, '; '.join(steps))


def cmd_group(a):
    wd = W / 'groups'
    wd.mkdir(exist_ok=True)
    if (wd / f'{a.name}.lean').exists():
        sys.exit(f'refused: {a.name} exists')
    (wd / 'sat').mkdir(exist_ok=True)
    p = pkg_env(a.pkg, wd)
    mods = [it.split(':')[0] for it in a.items]
    (wd / f'{a.name}.lean').write_text('import NativeTrust\nimport BVS\n' + ''.join(f'import {esc(m)}\n' for m in mods) + OPTS +
                                       f'set_option bvs4.workdir "{wd / "sat"}"\nset_option bvs4.timeout 600\n'
                                       f'set_option bvs4.log "{wd / (a.name + ".progress")}"\n'
                                       'bvs5_group ' + ' '.join(f'"{it}"' for it in a.items) + '\n')
    rc, wall, pk = run1(p, wd, f'{a.name}.lean', f'{a.name}.olean', wd / f'{a.name}.log', a.timeout)
    txt = (wd / f'{a.name}.log').read_text(errors='ignore')
    unsat = ' | '.join(l for l in txt.splitlines() if l.startswith('BVS_UNSAT'))[:900]
    done = ' | '.join(l for l in txt.splitlines() if l.startswith('BVS_DONE'))[:300]
    verdict, chk = 'FAILED', ''
    if rc == 0 and done:
        c = check(p, wd, a.name, mods, txt)
        chk = ' '.join(f'{k}={v}' for k, v in c.items())
        verdict = 'CONVERTED' if c['rc'] == 0 and c['facts'] == c['facts_std'] > 0 and c['users'] == c['users_std'] == c['types_same'] else 'CHECK_FAILED'
    row([a.name, a.pkg, 'group ' + ' '.join(a.items), verdict, f'group rc={rc} wall={wall:.0f} peak_kb={pk}', unsat, done, chk, p['nt']])
    print(a.name, verdict, f'rc={rc} wall={wall:.0f} peak_kb={pk}', chk)


def main():
    ap = argparse.ArgumentParser()
    sp = ap.add_subparsers(dest='cmd', required=True)
    s = sp.add_parser('shard')
    for x in ('name', 'pkg', 'module'):
        s.add_argument(x)
    s.add_argument('idx', type=int); s.add_argument('mode', choices=['shards', 'split'])
    s.add_argument('--k', type=int, default=4); s.add_argument('--seg', type=int, default=30000)
    s.add_argument('--par', type=int, default=4); s.add_argument('--timeout', type=int, default=3600)
    g = sp.add_parser('group')
    g.add_argument('name'); g.add_argument('pkg'); g.add_argument('items', nargs='+')
    g.add_argument('--timeout', type=int, default=3600)
    a = ap.parse_args()
    if not re.match(r'^[A-Za-z0-9]+$', a.name) or a.pkg not in PKGS:
        sys.exit('bad name or package')
    {'shard': cmd_shard, 'group': cmd_group}[a.cmd](a)


if __name__ == '__main__':
    main()
