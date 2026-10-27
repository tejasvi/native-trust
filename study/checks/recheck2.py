#!/usr/bin/env python3
"""Independent re-check of converted native facts, v2 (run as ntbuild on the box).

usage: recheck2.py NAME PKG_DIR SAMPLE [--seed S] [--nt-root DIR] --export BIN [--checkers DIR] [--mem GB]
                   [--results-name R] [--extra-import M]... [--extra-path D]... [--per-module]

Takes a random sample of the facts that m2_axioms*.py proved for package NAME (results/R.ax.tsv, verdict PROVED),
proves them again in a module compiled to an olean (`prove_native_axiom_nth`, fuel route), exports the resulting
kernel theorems with their whole dependency closure (lean4export built for the package's toolchain), and runs two
independent checkers bundled with Lean 4.35: nanoda (a separate kernel; permitted axioms propext, Classical.choice,
Quot.sound, any other a hard error) and con-ron (never reduces proofs).

v2 changes: --per-module checks each source module of the sample in its own module and export (for packages whose
modules cannot all be imported together); nanoda runs single-threaded (its worker threads have a fixed stack and
overflowed on deep terms); con-ron's "declined" (input it does not support) is reported as DECLINED, not FAIL; an
empty export never counts as a pass.
Writes WORK/recheck/NAME/[gK/]{RC.lean, RC.log, rc.export, nanoda.txt, conron.txt} and summary.txt.
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import argparse, json, os, random, re, subprocess, time
from pathlib import Path

HOME = Path(NT_BOX)
ELAN = HOME / 'elan'


def esc(m):
    return '.'.join(c if re.match(r"^[A-Za-z_][A-Za-z0-9_'!?]*$", c) else f'«{c}»' for c in m.split('.'))


def sh(cmd, cwd, env, mem_gb, timeout, log):
    with open(log, 'w') as f:
        p = subprocess.run(['bash', '-c', f'ulimit -v {mem_gb * 1024 * 1024}; ulimit -s unlimited; exec timeout -k 30 {timeout} "$@"',
                            'x'] + [str(c) for c in cmd], cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT)
    return p.returncode


def check_group(a, todo, gw, lean, env):
    """Prove the facts of `todo` again in one module (directory gw), export, run the two checkers."""
    gw.mkdir(parents=True, exist_ok=True)
    mods = sorted({m for m, _, _ in todo})
    (gw / 'RC.lean').write_text('import NativeTrust\n' + ''.join(f'import {x}\n' for x in a.extra_import) +
                                ''.join(f'import {esc(m)}\n' for m in mods) +
                                'set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n' +
                                ''.join(f'prove_native_axiom_nth {esc(m)} {i} (config := {{ split := 8 }})\n' for m, _, i in todo))
    genv = dict(env); genv['LEAN_PATH'] = env['LEAN_PATH'] + ':' + str(gw)
    t0 = time.time()
    rc = sh([lean, '-j1', '--tstack=1048576', '-o', 'RC.olean', 'RC.lean'], gw, genv, 96, 3 * 3600, gw / 'RC.log')
    txt = (gw / 'RC.log').read_text(errors='ignore')
    thms = re.findall(r'PROVED `[^`]+` as `([^`]+)`', txt)
    failed = len(re.findall(r'^FAILED `', txt, re.M))
    lines = [f"[{gw.name}] modules={len(mods)} sampled={len(todo)} proved_again={len(thms)} failed={failed} "
             f"compile_rc={rc} compile_s={time.time() - t0:.0f}"]
    res = {'thms': len(thms), 'n_ok': 0, 'c_ok': 0, 'c_declined': 0}
    if thms:
        envx = dict(genv); envx['PATH'] = f"{lean.parent}:" + genv['PATH']   # lean4export runs `lean` itself
        t1 = time.time()
        with open(gw / 'rc.export', 'w') as f, open(gw / 'export.err', 'w') as e:
            p = subprocess.run(['bash', '-c', f'ulimit -v {96 * 1024 * 1024}; exec timeout 7200 "$@"', 'x', a.export, 'RC', '--'] + thms,
                               cwd=gw, env=envx, stdout=f, stderr=e)
        nlines = sum(1 for _ in open(gw / 'rc.export'))
        lines.append(f"[{gw.name}] export_rc={p.returncode} export_lines={nlines} export_s={time.time() - t1:.0f}")
        cfg = {"export_file_path": str(gw / 'rc.export'), "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
               "unpermitted_axiom_hard_error": True, "nat_extension": True, "string_extension": True,
               "print_success_message": True, "num_threads": 1}
        (gw / 'nanoda.json').write_text(json.dumps(cfg))
        rcn = sh(['/usr/bin/time', '-f', 'nanoda: %e s %M KB', Path(a.checkers) / 'nanoda_bin', gw / 'nanoda.json'], gw, genv, a.mem, 7200, gw / 'nanoda.txt')
        rcc = sh(['/usr/bin/time', '-f', 'con-ron: %e s %M KB', Path(a.checkers) / 'con-ron', gw / 'rc.export'], gw, genv, a.mem, 7200, gw / 'conron.txt')
        nt = (gw / 'nanoda.txt').read_text(errors='ignore'); ct = (gw / 'conron.txt').read_text(errors='ignore')
        mn = re.search(r'Checked (\d+) declarations with no typechecker errors', nt)
        mc = re.search(r'accepted (\d+) declarations', ct)
        declined = re.search(r'con-ron: declined: ([^\n]*)', ct)
        ok_n = rcn == 0 and mn is not None and int(mn.group(1)) > 0
        ok_c = rcc == 0 and mc is not None and int(mc.group(1)) > 0
        cv = 'PASS' if ok_c else ('DECLINED' if declined else 'FAIL')
        lines.append(f"[{gw.name}] VERDICT nanoda={'PASS' if ok_n else 'FAIL'}({mn.group(1) if mn else 0} decls) "
                     f"con-ron={cv}({mc.group(1) if mc else 0} decls) kernel_theorems={len(thms)}"
                     + (f" con-ron-declined: {declined.group(1)[:120]}" if declined and not ok_c else ''))
        res.update(n_ok=int(ok_n), c_ok=int(ok_c), c_declined=int(bool(declined) and not ok_c))
    return lines, res


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name'); ap.add_argument('pkg'); ap.add_argument('sample', type=int)
    ap.add_argument('--seed', type=int, default=20261023)
    ap.add_argument('--nt-root', default=str(HOME / 'nt14'))
    ap.add_argument('--export', required=True)
    ap.add_argument('--checkers', default=str(ELAN / 'toolchains/leanprover--lean4---v4.35.0/bin'))
    ap.add_argument('--mem', type=int, default=200)
    ap.add_argument('--results-name', default=None)
    ap.add_argument('--extra-import', action='append', default=[])
    ap.add_argument('--extra-path', action='append', default=[])
    ap.add_argument('--per-module', action='store_true')
    a = ap.parse_args()
    pkg = Path(a.pkg).resolve()
    tc = (pkg / 'lean-toolchain').read_text().strip().split(':')[-1]
    lean = ELAN / 'toolchains' / f"leanprover--lean4---{tc}" / 'bin' / 'lean'
    w = HOME / 'work' / 'recheck2' / a.name; w.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ); env['ELAN_HOME'] = str(ELAN); env['PATH'] = f"{ELAN}/bin:" + env.get('PATH', '')
    env['LEAN_NUM_THREADS'] = '1'
    lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=pkg, env=env, capture_output=True, text=True).stdout.strip()
    env['LEAN_PATH'] = ':'.join([str(Path(a.nt_root) / tc / '.lake/build/lib/lean'), lp] + a.extra_path)
    rname = a.results_name or a.name
    last = {}
    for line in (HOME / 'results' / f"{rname}.ax.tsv").read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) >= 6:
            last[(c[1], c[2])] = c[5]
    proved = sorted(k for k, v in last.items() if v == 'PROVED')
    random.seed(a.seed)
    pick = random.sample(proved, min(a.sample, len(proved)))
    idx = {}
    for m in sorted({m for m, _ in pick}):
        lg = HOME / 'work' / rname / f"listax_{m}.log"
        for l in lg.read_text(errors='ignore').splitlines():
            c = l.split('\t')
            if c[0] == 'AX' and len(c) >= 5:
                idx[(m, c[1])] = int(c[4])
    todo = [(m, ax, idx[(m, ax)]) for m, ax in pick if (m, ax) in idx]
    groups = [todo]
    if a.per_module:
        by = {}
        for t in todo:
            by.setdefault(t[0], []).append(t)
        groups = list(by.values())
    summary = [f"name={a.name} toolchain={tc} sampled={len(todo)} groups={len(groups)}"]
    tot = dict(thms=0, n_ok=0, c_ok=0, c_declined=0)
    for gi, grp in enumerate(groups):
        lines, res = check_group(a, grp, w / (f"g{gi}" if a.per_module else "all"), lean, env)
        summary += lines
        for k in tot:
            tot[k] += res[k]
    summary.append(f"TOTAL groups={len(groups)} kernel_theorems={tot['thms']} nanoda_pass_groups={tot['n_ok']} "
                   f"con-ron_pass_groups={tot['c_ok']} con-ron_declined_groups={tot['c_declined']}")
    (w / 'summary.txt').write_text('\n'.join(summary) + '\n')
    print('\n'.join(summary))


if __name__ == '__main__':
    main()
