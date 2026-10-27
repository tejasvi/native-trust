#!/usr/bin/env python3
"""Independent re-check of converted native facts (run as ntbuild on the box).

usage: recheck.py NAME PKG_DIR SAMPLE [--seed S] [--nt-root DIR] [--export BIN] [--checkers DIR] [--mem GB]

Takes a random sample of the facts that m2_axioms*.py proved for package NAME (results/NAME.ax.tsv, verdict
PROVED), proves them again in ONE module compiled to an olean (`prove_native_axiom_nth`, fuel route), exports the
resulting kernel theorems and their whole dependency closure with lean4export (built for the package's toolchain),
and runs two independent checkers bundled with Lean 4.35 on the export: nanoda (a separate kernel, permitted
axioms = propext, Classical.choice, Quot.sound, any other axiom a hard error) and con-ron (which never reduces
proofs). Writes WORK/recheck/NAME/{RC.lean, RC.log, rc.export, nanoda.txt, conron.txt, summary.txt}.
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import argparse, json, os, random, re, subprocess, sys, time
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


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name'); ap.add_argument('pkg'); ap.add_argument('sample', type=int)
    ap.add_argument('--seed', type=int, default=20261023)
    ap.add_argument('--nt-root', default=str(HOME / 'nt14'))
    ap.add_argument('--export', required=True)
    ap.add_argument('--checkers', default=str(ELAN / 'toolchains/leanprover--lean4---v4.35.0/bin'))
    ap.add_argument('--mem', type=int, default=200)
    ap.add_argument('--results-name', default=None, help='results file to sample from (default NAME)')
    ap.add_argument('--extra-import', action='append', default=[], help='module imported by the re-check (e.g. @[kernel_fact] proofs)')
    ap.add_argument('--extra-path', action='append', default=[])
    a = ap.parse_args()
    pkg = Path(a.pkg).resolve()
    tc = (pkg / 'lean-toolchain').read_text().strip().split(':')[-1]
    lean = ELAN / 'toolchains' / f"leanprover--lean4---{tc}" / 'bin' / 'lean'
    if not lean.exists():
        lean = ELAN / 'toolchains' / f"leanprover--lean4-nightly---{tc}" / 'bin' / 'lean'
    w = HOME / 'work' / 'recheck' / a.name; w.mkdir(parents=True, exist_ok=True)
    env = dict(os.environ); env['ELAN_HOME'] = str(ELAN); env['PATH'] = f"{ELAN}/bin:" + env.get('PATH', '')
    env['LEAN_NUM_THREADS'] = '1'
    lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=pkg, env=env, capture_output=True, text=True).stdout.strip()
    env['LEAN_PATH'] = ':'.join([str(Path(a.nt_root) / tc / '.lake/build/lib/lean'), lp, str(w)] + a.extra_path)
    # sample proved facts (module, index) from the listing logs of the study
    res = HOME / 'results' / f"{a.results_name or a.name}.ax.tsv"
    last = {}
    for line in res.read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) >= 6:
            last[(c[1], c[2])] = c[5]
    proved = sorted(k for k, v in last.items() if v == 'PROVED')
    random.seed(a.seed)
    pick = random.sample(proved, min(a.sample, len(proved)))
    # indices of the sampled axioms, from the per-module listings (#native_axioms)
    idx = {}
    work_pkg = HOME / 'work' / (a.results_name or a.name)
    for m in sorted({m for m, _ in pick}):
        lg = work_pkg / f"listax_{m}.log"
        for l in lg.read_text(errors='ignore').splitlines():
            c = l.split('\t')
            if c[0] == 'AX' and len(c) >= 5:
                idx[(m, c[1])] = int(c[4])
    todo = [(m, ax, idx[(m, ax)]) for m, ax in pick if (m, ax) in idx]
    src = w / 'RC.lean'
    mods = sorted({m for m, _, _ in todo})
    src.write_text('import NativeTrust\n' + ''.join(f'import {x}\n' for x in a.extra_import) +
                   ''.join(f'import {esc(m)}\n' for m in mods) +
                   'set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n' +
                   ''.join(f'prove_native_axiom_nth {esc(m)} {i} (config := {{ split := 8 }})\n' for m, _, i in todo))
    t0 = time.time()
    rc = sh([lean, '-j1', '--tstack=1048576', '-o', 'RC.olean', 'RC.lean'], w, env, 96, 3 * 3600, w / 'RC.log')
    txt = (w / 'RC.log').read_text(errors='ignore')
    thms = re.findall(r'PROVED `[^`]+` as `([^`]+)`', txt)
    failed = len(re.findall(r'^FAILED `', txt, re.M))
    summary = [f"name={a.name} toolchain={tc} sampled={len(todo)} proved_again={len(thms)} failed={failed} "
               f"compile_rc={rc} compile_s={time.time() - t0:.0f}"]
    if thms:
        t1 = time.time()
        # lean4export runs `lean` itself: the package's toolchain must come first on PATH
        envx = dict(env); envx['PATH'] = f"{lean.parent}:" + env['PATH']
        with open(w / 'rc.export', 'w') as f, open(w / 'export.err', 'w') as e:
            p = subprocess.run(['bash', '-c', f'ulimit -v {96 * 1024 * 1024}; exec timeout 7200 "$@"', 'x', a.export, 'RC', '--'] + thms,
                               cwd=w, env=envx, stdout=f, stderr=e)
        lines = sum(1 for _ in open(w / 'rc.export'))
        summary.append(f"export_rc={p.returncode} export_lines={lines} export_s={time.time() - t1:.0f}")
        cfg = {"export_file_path": str(w / 'rc.export'), "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
               "unpermitted_axiom_hard_error": True, "nat_extension": True, "string_extension": True,
               "print_success_message": True, "num_threads": 16}
        (w / 'nanoda.json').write_text(json.dumps(cfg))
        t2 = time.time()
        rcn = sh(['/usr/bin/time', '-f', 'nanoda: %e s %M KB', Path(a.checkers) / 'nanoda_bin', w / 'nanoda.json'], w, env, a.mem, 7200, w / 'nanoda.txt')
        summary.append(f"nanoda_rc={rcn} :: " + ' | '.join(l.strip() for l in (w / 'nanoda.txt').read_text(errors='ignore').splitlines()[-3:]))
        rcc = sh(['/usr/bin/time', '-f', 'con-ron: %e s %M KB', Path(a.checkers) / 'con-ron', w / 'rc.export'], w, env, a.mem, 7200, w / 'conron.txt')
        summary.append(f"con-ron_rc={rcc} :: " + ' | '.join(l.strip() for l in (w / 'conron.txt').read_text(errors='ignore').splitlines()[-2:]))
        summary.append(f"checkers_s={time.time() - t2:.0f}")
        # a verdict needs a non-empty check: an empty export "passes" both checkers vacuously
        nt = (w / 'nanoda.txt').read_text(errors='ignore'); ct = (w / 'conron.txt').read_text(errors='ignore')
        mn = re.search(r'Checked (\d+) declarations with no typechecker errors', nt)
        mc = re.search(r'accepted (\d+) declarations', ct)
        ok_n = rcn == 0 and mn is not None and int(mn.group(1)) > 0
        ok_c = rcc == 0 and mc is not None and int(mc.group(1)) > 0
        summary.append(f"VERDICT nanoda={'PASS' if ok_n else 'FAIL'}({mn.group(1) if mn else 0} decls) "
                       f"con-ron={'PASS' if ok_c else 'FAIL'}({mc.group(1) if mc else 0} decls) kernel_theorems={len(thms)}")
    (w / 'summary.txt').write_text('\n'.join(summary) + '\n')
    print('\n'.join(summary))


if __name__ == '__main__':
    main()
