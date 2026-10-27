#!/usr/bin/env python3
"""M2 per-axiom driver v3 (m2_axioms3.py) for one Lean package (run as the unprivileged user ntbuild on the box).

usage: m2_axioms3.py NAME PKG_DIR [--jobs J] [--fact-timeout S] [--fact-mem GB] [--split K] [--build-timeout S]
                     [--skip-build] [--redo] [--include RE] [--exclude RE] [--nt-root DIR]
                     [--extra-import MOD]... [--extra-path DIR]... [--results-suffix S]

v3 (from v2): NativeTrust nt11; a phase-2 check imports only the phase-1 modules whose fact lies in the import
closure of its own module (v2 imported every phase-1 module, and packages with alternative generated modules
that define the same names, such as TrainVerify, failed with "environment already contains").

v2 (from m2_axioms.py): NativeTrust nt9 (facts behind instances, including instances of `Prop` classes such as
`Fact (Nat.Prime p)`, and public declarations whose axioms have private names, are phase-1 facts;
`@[kernel_fact]`); --extra-import adds modules to every check file (for instance a module of `@[kernel_fact]`
proofs: a remedy experiment, reported separately with --results-suffix).

The unit is the native fact: one `native_decide`/`bv_decide` axiom (one tactic call), not the theorem. The
per-theorem drivers (m2_repo*.py) re-proved a fact once for every theorem that depends on it, in separate
processes (a fact inside a definition used by 14 theorems was proved 14 times).

1. build as m2_repo4.py (modules whose source mentions native evaluation; `lake build`, Mathlib cache);
2. `#native_axioms M` per built module: (module, axiom, tactic, inner, index); `inner` = used inside a
   definition, so other facts' statements can mention it;
3. phase 1: each inner axiom, `prove_native_axiom_nth M i` in its own process, compiled with `-o` to a module
   F1_<k> in WORK/NAME/mods (the proof is registered in the olean);
4. phase 2: each other axiom in its own process, importing every phase-1 module that proved its axiom, so
   nested facts are reused instead of re-proved.
Each process: `set_option nativeTrust.eprint true` and `trace := true`, so the static blockers and the phase
times reach the log at once, even when the process is stopped by the time or memory limit.
Results: RESULTS/NAME.ax.tsv, one line per axiom as each process ends:
package, module, axiom, tactic, inner, verdict (PROVED|FAILED|TIMEOUT|ERROR|NOT_BUILT), reason, kernel_ms,
maxrss_kb, secs, blockers, trace
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import argparse, concurrent.futures as cf, os, re, signal, subprocess, sys, time
from pathlib import Path

HOME = Path(NT_BOX)
ELAN = HOME / 'elan'
RESULTS = HOME / 'results'
WORK = HOME / 'work'
NATIVE_RE = re.compile(r'native_decide|decide\s*\+native|native\s*:=\s*true|bv_decide|ofReduceBool|ofReduceNat')
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*$")


def toolchain_of(pkg: Path) -> str:
    return (pkg / 'lean-toolchain').read_text().strip().split(':')[-1]


def env_for(tc: str) -> dict:
    e = dict(os.environ)
    e['ELAN_HOME'] = str(ELAN)
    e['PATH'] = f"{ELAN}/bin:" + e.get('PATH', '/usr/bin:/bin')
    e['LEAN_NUM_THREADS'] = '1'
    return e


def run(cmd, cwd, env, timeout, mem_gb, log):
    """Run under an address-space cap and a time limit; return (rc, seconds), rc 124 on timeout. The limit is
    enforced by coreutils `timeout` on its whole process group (v1-v3 killed only the direct child, so a timed
    out `lean` kept running under `/usr/bin/time`), with a process-group kill as a backstop."""
    t0 = time.time()
    with open(log, 'a') as f:
        f.write(f"$ {' '.join(map(str, cmd))}\n"); f.flush()
        p = subprocess.Popen(['bash', '-c', f'ulimit -n 65536 2>/dev/null || ulimit -n $(ulimit -Hn); ulimit -v {mem_gb * 1024 * 1024}; '
                              f'exec timeout -k 30 {timeout} "$@"', 'cap'] + [str(c) for c in cmd],
                             cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, start_new_session=True)
        try:
            rc = p.wait(timeout=timeout + 120)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL); p.wait(); rc = 124
        if rc == 137 and time.time() - t0 >= timeout:
            rc = 124
        f.write(f"rc={rc} secs={time.time() - t0:.0f}\n")
    return rc, time.time() - t0


def src_dirs(pkg: Path):
    """All `srcDir` values of the package's libraries (each lib may set its own)."""
    out = []
    for lf in ('lakefile.toml', 'lakefile.lean'):
        p = pkg / lf
        if p.exists():
            out += [pkg / m for m in re.findall(r'srcDir\s*(?::=|=)\s*"([^"]+)"', p.read_text())]
    return [d for d in out if d.resolve() != pkg.resolve()]


def native_files(pkg: Path):
    out = []
    for f in pkg.rglob('*.lean'):
        if '.lake' in f.parts or 'lake-packages' in f.parts:
            continue
        try:
            if NATIVE_RE.search(f.read_text(errors='ignore')):
                out.append(f)
        except OSError:
            pass
    return sorted(out)


def pkg_root_of(f: Path, pkg: Path) -> Path:
    """The nearest enclosing Lake package of file `f` (nested path dependencies such as `ext/foo/` have
    their own lakefile and module names relative to their own source roots)."""
    d = f.parent
    while d != pkg and pkg in d.parents:
        if (d / 'lakefile.toml').exists() or (d / 'lakefile.lean').exists():
            return d
        d = d.parent
    return pkg


def module_of(f: Path, root: Path):
    """Module name of file `f`: relative to the library source root of its package it lies under (a lib's
    `srcDir`), else relative to the package root."""
    for r in src_dirs(root):
        try:
            return '.'.join(f.relative_to(r).with_suffix('').parts)
        except ValueError:
            pass
    try:
        return '.'.join(f.relative_to(root).with_suffix('').parts)
    except ValueError:
        return None


def esc(m: str) -> str:
    """Module name as Lean/Lake syntax: components that are not identifiers are wrapped in «»."""
    return '.'.join(c if IDENT_RE.match(c) else f'«{c}»' for c in m.split('.'))


def lean_path(pkg: Path, nt: Path, env) -> list:
    """NativeTrust first, then the package's own search path as Lake computes it (path dependencies such as
    `../../mathlib4` or `ext/foo` included); falls back to the package's `.lake/packages`."""
    parts = []
    try:
        p = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=pkg, env=env, capture_output=True,
                           text=True, timeout=600)
        if p.returncode == 0:
            parts = [x for x in p.stdout.strip().split(':') if x]
    except subprocess.TimeoutExpired:
        pass
    if not parts:
        parts = [str(pkg / '.lake/build/lib/lean')] + [str(d) for d in sorted((pkg / '.lake/packages').glob('*/.lake/build/lib/lean'))]
    return [str(nt / '.lake/build/lib/lean')] + parts


def done_keys(out: Path, final=('KERNELIZED', 'CLEAN', 'REJECTED')):
    """(module, theorem) whose last verdict in the results is in `final`."""
    last = {}
    if out.exists():
        for line in out.read_text(errors='ignore').splitlines():
            c = line.split('\t')
            if len(c) >= 4:
                last[(c[1], c[2])] = c[3]
    return {k for k, v in last.items() if v in final}



def classify(rc, txt, fact_timeout):
    verdict = 'TIMEOUT' if rc == 124 else 'ERROR'
    if re.search(r'\bPROVED `', txt):
        verdict = 'PROVED'
    elif re.search(r'\bFAILED `', txt):
        verdict = 'FAILED'
    reason = ''
    if verdict == 'FAILED':
        if 'evaluates the decision procedure to `false`' in txt: reason = 'false_in_logic'
        elif 'non-standard axioms' in txt: reason = 'other_axiom'
        elif 'deterministic timeout' in txt and 'evaluation was bounded' in txt: reason = 'blocked'
        elif 'cannot unfold' in txt: reason = 'blocked'
        elif 'deterministic timeout' in txt: reason = 'heartbeats'
        elif 'internal error' in txt: reason = 'bridge'
        else: reason = 'other'
    elif verdict == 'ERROR':
        if 'maximum recursion depth' in txt: reason = 'maxRecDepth'
        elif 'deep recursion' in txt: reason = 'deep_recursion'
        elif 'Stack overflow' in txt or 'stack overflow' in txt: reason = 'stack'
        elif 'out of memory' in txt or 'std::bad_alloc' in txt or rc in (134, 137): reason = 'memory'
        else: reason = f'rc{rc}'
    elif verdict == 'TIMEOUT':
        reason = f'{fact_timeout}s'
    return verdict, reason


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name'); ap.add_argument('pkg')
    ap.add_argument('--jobs', type=int, default=32)
    ap.add_argument('--fact-timeout', type=int, default=900)
    ap.add_argument('--fact-mem', type=int, default=48)
    ap.add_argument('--split', type=int, default=8)
    ap.add_argument('--build-timeout', type=int, default=10800)
    ap.add_argument('--skip-build', action='store_true')
    ap.add_argument('--redo', action='store_true', help='re-check axioms whose last verdict is not PROVED')
    ap.add_argument('--include', default='', help='only axioms whose name matches this regex')
    ap.add_argument('--exclude', default='', help='skip axioms whose name matches this regex')
    ap.add_argument('--build-threads', type=int, default=16)
    ap.add_argument('--nt-root', default=str(HOME / 'nt11'))
    ap.add_argument('--extra-import', action='append', default=[])
    ap.add_argument('--extra-path', action='append', default=[])
    ap.add_argument('--results-suffix', default='')
    a = ap.parse_args()
    pkg = Path(a.pkg).resolve(); tc = toolchain_of(pkg); env = env_for(tc)
    nt = Path(a.nt_root) / tc
    lean = ELAN / 'toolchains' / f"leanprover--lean4---{tc}" / 'bin' / 'lean'
    w = WORK / a.name; w.mkdir(parents=True, exist_ok=True); RESULTS.mkdir(exist_ok=True)
    mods_dir = w / 'mods'; mods_dir.mkdir(exist_ok=True)
    log = w / f'driver_ax{a.results_suffix}.log'
    out = RESULTS / f"{a.name}{a.results_suffix}.ax.tsv"
    files = native_files(pkg)
    mods = sorted({m for m in (module_of(f, pkg_root_of(f, pkg)) for f in files) if m})
    with open(log, 'a') as f:
        f.write(f"{time.strftime('%FT%TZ', time.gmtime())} ax pkg={pkg} tc={tc} nt={nt} native_files={len(files)} modules={len(mods)}\n")
    if not (nt / '.lake/build/lib/lean/NativeTrust.olean').exists():
        print(f"no NativeTrust build in {nt}", file=sys.stderr); sys.exit(2)
    lp = lean_path(pkg, nt, env)
    def has_olean(m):
        rel = m.replace('.', '/') + '.olean'
        return any((Path(d) / rel).exists() for d in lp[1:])
    if not a.skip_build:
        missing = [m for m in mods if not has_olean(m)]
        if missing:
            if (pkg / 'lake-manifest.json').exists() and 'mathlib' in (pkg / 'lake-manifest.json').read_text(errors='ignore').lower():
                run(['lake', 'exe', 'cache', 'get'], pkg, env, 3600, 64, w / 'cache_ax.log')
            benv = dict(env); benv['LEAN_NUM_THREADS'] = str(a.build_threads)
            run(['lake', 'build'] + [esc(m) for m in missing], pkg, benv, a.build_timeout, 400, w / 'build_ax.log')
            for m in [m for m in missing if not has_olean(m)]:
                run(['lake', 'build', esc(m)], pkg, benv, a.build_timeout, 400, w / 'build_ax_single.log')
    built = {m for m in mods if has_olean(m)}
    with open(out, 'a') as f:
        for m in mods:
            if m not in built:
                f.write(f"{a.name}\t{m}\t-\t\t\tNOT_BUILT\t\t\t\t\t\t\n")
    env['LEAN_PATH'] = ':'.join(lp + [str(mods_dir)] + a.extra_path)
    # 2. axioms per module
    closure = {}
    def list_axioms(m):
        lf = w / f"listax_{m}.lean"
        lf.write_text(f"import NativeTrust\nimport {esc(m)}\n#native_axioms {esc(m)}\nopen Lean in\n"
                      f"#eval show CoreM Unit from do\n  for n in (← getEnv).header.moduleNames do IO.println s!\"MOD\\t{{n}}\"\n")
        lg = w / f"listax_{m}.log"
        if lg.exists():
            lg.unlink()
        run([lean, '-j1', lf], w, env, 1800, 64, lg)
        rows = []
        mods_in = set()
        for l in lg.read_text(errors='ignore').splitlines():
            c = l.split('\t')
            if c[0] == 'AX' and len(c) >= 5:
                rows.append((m, c[1], c[2], c[3] == 'true', int(c[4])))
            elif c[0] == 'MOD' and len(c) >= 2:
                mods_in.add(c[1])
        closure[m] = mods_in
        return rows
    axs = []
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for r in ex.map(list_axioms, sorted(built)):
            axs += r
    last = {}
    if out.exists():
        for line in out.read_text(errors='ignore').splitlines():
            c = line.split('\t')
            if len(c) >= 6:
                last[(c[1], c[2])] = c[5]
    def wanted(t):
        if a.redo and last.get((t[0], t[1])) == 'PROVED':
            return False
        if not a.redo and (t[0], t[1]) in last:
            return False
        return (not a.include or re.search(a.include, t[1])) and not (a.exclude and re.search(a.exclude, t[1]))
    # every inner axiom gets a phase-1 module (also when proved before: phase 2 imports it)
    inner = [t for t in axs if t[3]]
    outer = [t for t in axs if not t[3] and wanted(t)]
    with open(log, 'a') as f:
        f.write(f"native axioms={len(axs)} inner={len(inner)} outer_todo={len(outer)}\n")
    cfgs = f"(config := {{ split := {a.split}, trace := true }})"
    def check(t, phase, imports):
        m, axn, tac, inn, i = t
        safe = re.sub(r'[^A-Za-z0-9_]', '_', f"{m}_{i}")[:150]
        modname = f"F{phase}{a.results_suffix.replace('.', '_')}_{safe}"
        src = mods_dir / f"{modname}.lean"
        src.write_text(f"import NativeTrust\nimport {esc(m)}\n" + ''.join(f"import {x}\n" for x in a.extra_import + imports) +
                       f"set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"
                       f"set_option nativeTrust.eprint true\nprove_native_axiom_nth {esc(m)} {i} {cfgs}\n")
        lg = w / f"ax{phase}{a.results_suffix}_{safe}.log"
        if lg.exists():
            lg.unlink()
        olean = mods_dir / f"{modname}.olean"
        if olean.exists():
            olean.unlink()
        cmd = ['/usr/bin/time', '-f', 'maxrss_kb %M', lean, '-j1', '--tstack=1048576']
        if phase == 1:
            cmd += ['-o', olean.name]
        rc, secs = run(cmd + [src.name], mods_dir, env, a.fact_timeout, a.fact_mem, lg)
        txt = lg.read_text(errors='ignore')
        verdict, reason = classify(rc, txt, a.fact_timeout)
        blockers = ';'.join(sorted(set(re.findall(r'• `([^`]+)`', txt))))[:400]
        rss = re.search(r'maxrss_kb (\d+)', txt)
        kms = re.search(r'kernel_ms=(\d+)', txt)
        nt_lines = [l for l in txt.splitlines() if l.startswith('NT ')]
        tr = f"nt_lines={len(nt_lines)}"
        if nt_lines:
            tr += ' last=' + re.sub(r'^NT \S+ ', '', nt_lines[-1])[:120]
        line = (f"{a.name}\t{m}\t{axn}\t{tac}\t{inn}\t{verdict}\t{reason}\t{kms.group(1) if kms else ''}\t"
                f"{rss.group(1) if rss else ''}\t{secs:.0f}\t{blockers}\t{tr}\n")
        with open(out, 'a') as f:
            f.write(line)
        return verdict, (modname if phase == 1 and verdict == 'PROVED' and olean.exists() else None)
    # 3. phase 1
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        r1 = list(ex.map(lambda t: check(t, 1, []), inner))
    # phase-1 module of each proved inner fact, by the module that declares the fact
    proved = [(t[0], mn) for t, (_, mn) in zip(inner, r1) if mn]
    def imports_for(m):
        cl = closure.get(m, set())
        return [mn for (src, mn) in proved if src == m or src in cl]
    # 4. phase 2
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        r2 = list(ex.map(lambda t: check(t, 2, imports_for(t[0])), outer))
    verdicts = [v for (v, _) in r1 + r2]
    with open(log, 'a') as f:
        f.write(f"{time.strftime('%FT%TZ', time.gmtime())} summary " + ' '.join(f"{v}={verdicts.count(v)}" for v in sorted(set(verdicts))) + '\n')
    print(a.name, len(verdicts), 'axioms:', {v: verdicts.count(v) for v in set(verdicts)})


if __name__ == '__main__':
    main()
