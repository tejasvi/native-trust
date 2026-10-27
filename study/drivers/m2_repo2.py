#!/usr/bin/env python3
"""M2 driver v2 for one Lean package (run as the unprivileged user ntbuild on the box).

usage: m2_repo2.py NAME PKG_DIR [--jobs J] [--fact-timeout S] [--fact-mem GB] [--split K] [--build-timeout S]
                   [--skip-build] [--only-new] [--nt-root DIR]

Changes from m2_repo.py (v1):
- direct uses come from `#native_theorems` of NativeTrust src2 (axiom referenced by the theorem's own proof
  term): v1 missed module-system packages (private axiom names), legacy toolchains (an internal auxiliary
  lemma carries `Lean.ofReduceBool`) and facts inside definitions (`_proof_i`);
- facts are addressed by index (`trust_check_nth M i`), so private and internal theorems are reachable;
- module names with non-identifier components (`FormalConjectures.ErdosProblems.307`) are escaped with «»;
- files are selected by `native_decide`, `decide +native`, `native := true`, `bv_decide`, `ofReduceBool/Nat`;
- each row also records the number of direct/all native axioms and the tactic that made each direct axiom;
- --only-new skips theorems that already have a final verdict (KERNELIZED/CLEAN/REJECTED) in the results.

1. lake exe cache get (if the package depends on Mathlib), 2. lake build of the selected modules that have no
olean yet, 3. #native_theorems per module, 4. one process per theorem with a direct use:
#kernel_blockers_nth (static) then trust_check_nth (kernel), under time and memory limits.
Results: one line per fact in RESULTS/NAME.tsv as each process ends (nothing is lost on a timeout).
columns: package, module, theorem, verdict, reason, kernel_ms, maxrss_kb, secs, blockers, n_direct, n_all, tactics
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import argparse, concurrent.futures as cf, os, re, subprocess, sys, time
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
    """Run under an address-space cap; return (rc, seconds)."""
    t0 = time.time()
    with open(log, 'a') as f:
        f.write(f"$ {' '.join(map(str, cmd))}\n"); f.flush()
        try:
            p = subprocess.run(['bash', '-c', f'ulimit -n 65536 2>/dev/null || ulimit -n $(ulimit -Hn); ulimit -v {mem_gb * 1024 * 1024}; exec "$@"', 'cap'] + [str(c) for c in cmd],
                               cwd=cwd, env=env, stdout=f, stderr=subprocess.STDOUT, timeout=timeout)
            rc = p.returncode
        except subprocess.TimeoutExpired:
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


def done_keys(out: Path):
    keys = set()
    if out.exists():
        for line in out.read_text(errors='ignore').splitlines():
            c = line.split('\t')
            if len(c) >= 4 and c[3] in ('KERNELIZED', 'CLEAN', 'REJECTED'):
                keys.add((c[1], c[2]))
    return keys


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name'); ap.add_argument('pkg')
    ap.add_argument('--jobs', type=int, default=32)
    ap.add_argument('--fact-timeout', type=int, default=900)
    ap.add_argument('--fact-mem', type=int, default=48)
    ap.add_argument('--split', type=int, default=8)
    ap.add_argument('--build-timeout', type=int, default=10800)
    ap.add_argument('--skip-build', action='store_true')
    ap.add_argument('--only-new', action='store_true')
    ap.add_argument('--build-threads', type=int, default=16)
    ap.add_argument('--nt-root', default=str(HOME / 'nt2'))
    a = ap.parse_args()
    pkg = Path(a.pkg).resolve(); tc = toolchain_of(pkg); env = env_for(tc)
    nt = Path(a.nt_root) / tc
    lean = ELAN / 'toolchains' / f"leanprover--lean4---{tc}" / 'bin' / 'lean'
    w = WORK / a.name; w.mkdir(parents=True, exist_ok=True); RESULTS.mkdir(exist_ok=True)
    log = w / 'driver2.log'
    out = RESULTS / f"{a.name}.tsv"
    files = native_files(pkg)
    mods = sorted({m for m in (module_of(f, pkg_root_of(f, pkg)) for f in files) if m})
    with open(log, 'a') as f:
        f.write(f"{time.strftime('%FT%TZ', time.gmtime())} v2 pkg={pkg} tc={tc} nt={nt} native_files={len(files)} modules={len(mods)}\n")
    if not (nt / '.lake/build/lib/lean/NativeTrust.olean').exists():
        print(f"no NativeTrust build in {nt}", file=sys.stderr); sys.exit(2)

    lp = lean_path(pkg, nt, env)
    def has_olean(m):
        rel = m.replace('.', '/') + '.olean'
        return any((Path(d) / rel).exists() for d in lp[1:])
    # 1-2. cache + targeted build of the modules without an olean (failures are recorded, the rest continue)
    if not a.skip_build:
        missing = [m for m in mods if not has_olean(m)]
        if missing:
            if (pkg / 'lake-manifest.json').exists() and 'mathlib' in (pkg / 'lake-manifest.json').read_text(errors='ignore').lower():
                run(['lake', 'exe', 'cache', 'get'], pkg, env, 3600, 64, w / 'cache2.log')
            # Lake's job parallelism follows LEAN_NUM_THREADS
            benv = dict(env); benv['LEAN_NUM_THREADS'] = str(a.build_threads)
            run(['lake', 'build'] + [esc(m) for m in missing], pkg, benv, a.build_timeout, 400, w / 'build2.log')
            # a module outside every library makes a bulk `lake build` fail early: retry the missing ones alone
            for m in [m for m in missing if not has_olean(m)]:
                run(['lake', 'build', esc(m)], pkg, benv, a.build_timeout, 400, w / 'build2_single.log')
    built = {m for m in mods if has_olean(m)}
    with open(out, 'a') as f:
        for m in mods:
            if m not in built:
                f.write(f"{a.name}\t{m}\t-\tNOT_BUILT\t\t\t\n")
    # 3. theorems per built module: (module, name, direct, all, index)
    env['LEAN_PATH'] = ':'.join(lp)
    def list_thms(m):
        lf = w / f"list2_{m}.lean"; lf.write_text(f"import NativeTrust\nimport {esc(m)}\n#native_theorems {esc(m)}\n")
        lg = w / f"list2_{m}.log"
        if lg.exists():
            lg.unlink()
        run([lean, '-j1', lf], w, env, 1800, 64, lg)
        rows = []
        for l in lg.read_text(errors='ignore').splitlines():
            c = l.split('\t')
            if c[0] == 'THM' and len(c) >= 5:
                rows.append((m, c[1], int(c[2]), int(c[3]), int(c[4])))
        return rows
    thms = []
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for r in ex.map(list_thms, sorted(built)):
            thms += r
    direct = [t for t in thms if t[2] > 0]
    skip = done_keys(out) if a.only_new else set()
    todo = [t for t in direct if (t[0], t[1]) not in skip]
    with open(log, 'a') as f:
        f.write(f"native theorems={len(thms)} direct facts={len(direct)} todo={len(todo)}\n")
    # 4. one process per fact
    def check(t):
        m, name, nd, na, i = t
        safe = re.sub(r'[^A-Za-z0-9_.]', '_', f"{m}.{i}")[:150]
        cf_ = w / f"chk2_{safe}.lean"
        cf_.write_text(f"import NativeTrust\nimport {esc(m)}\nset_option Elab.async false\nset_option maxHeartbeats 0\n"
                       f"set_option maxRecDepth 1000000\n#kernel_blockers_nth {esc(m)} {i}\n"
                       f"trust_check_nth {esc(m)} {i} (config := {{ split := {a.split} }})\n")
        lg = w / f"chk2_{safe}.log"
        if lg.exists():
            lg.unlink()
        rc, secs = run(['/usr/bin/time', '-f', 'maxrss_kb %M', lean, '-j1', '--tstack=1048576', cf_], w, env,
                       a.fact_timeout, a.fact_mem, lg)
        txt = lg.read_text(errors='ignore')
        verdict = 'TIMEOUT' if rc == 124 else 'ERROR'
        for v in ('KERNELIZED', 'CLEAN', 'REJECTED'):
            if re.search(rf'\b{v}\b `', txt):
                verdict = v; break
        reason = ''
        if verdict == 'REJECTED':
            if 'evaluates the decision procedure to `false`' in txt: reason = 'false_in_logic'
            elif 'non-standard axioms' in txt and 'native fact' not in txt: reason = 'other_axiom'
            elif 'cannot unfold' in txt: reason = 'blocked'
            elif 'ran out of resources' in txt or 'timeout' in txt: reason = 'resources'
            else: reason = 'other'
        blockers = ';'.join(sorted(set(re.findall(r'^• `([^`]+)`', txt, re.M))))[:300]
        rss = re.search(r'maxrss_kb (\d+)', txt)
        kms = re.search(r'kernel_ms=(\d+)', txt)
        # tactic of each axiom reported by #kernel_blockers_nth (`<decl>._native.<tactic>.ax…`)
        tac = {}
        for x in set(re.findall(r'^`([^`]*\._native\.([A-Za-z_]+)\.ax[^`]*)`:', txt, re.M)):
            tac[x[1]] = tac.get(x[1], 0) + 1
        if 'Lean.ofReduceBool' in txt and not tac:
            tac['ofReduceBool'] = 1
        tactics = ','.join(f"{k}:{v}" for k, v in sorted(tac.items()))
        line = (f"{a.name}\t{m}\t{name}\t{verdict}\t{reason}\t{kms.group(1) if kms else ''}\t"
                f"{rss.group(1) if rss else ''}\t{secs:.0f}\t{blockers}\t{nd}\t{na}\t{tactics}\n")
        with open(out, 'a') as f:
            f.write(line)
        return verdict
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        verdicts = list(ex.map(check, todo))
    with open(log, 'a') as f:
        f.write(f"{time.strftime('%FT%TZ', time.gmtime())} summary " + ' '.join(f"{v}={verdicts.count(v)}" for v in sorted(set(verdicts))) + '\n')
    print(a.name, len(todo), 'facts:', {v: verdicts.count(v) for v in set(verdicts)})


if __name__ == '__main__':
    main()
