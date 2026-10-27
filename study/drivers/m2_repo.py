#!/usr/bin/env python3
"""M2 driver for one Lean package (run as the unprivileged user ntbuild on the box).

usage: m2_repo.py NAME PKG_DIR [--jobs J] [--fact-timeout S] [--fact-mem GB] [--split K] [--build-timeout S]

1. lake exe cache get (if the package depends on Mathlib), 2. lake build of the modules that mention
native_decide, 3. #native_theorems per module, 4. one process per theorem that uses native_decide directly:
#kernel_blockers (static, prints at once) then trust_check (kernel), under time and memory limits.
Results: one line per fact in RESULTS/NAME.tsv as each process ends (nothing is lost on a timeout).
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import argparse, concurrent.futures as cf, os, re, subprocess, sys, time
from pathlib import Path

HOME = Path(NT_BOX)
ELAN = HOME / 'elan'
RESULTS = HOME / 'results'
WORK = HOME / 'work'


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
            if 'native_decide' in f.read_text(errors='ignore'):
                out.append(f)
        except OSError:
            pass
    return sorted(out)


def module_of(f: Path, pkg: Path, extra_roots):
    """Module name of file `f`: relative to the library source root it lies under (a lib's `srcDir`),
    else relative to the package root."""
    for r in extra_roots:
        try:
            return '.'.join(f.relative_to(r).with_suffix('').parts)
        except ValueError:
            pass
    try:
        return '.'.join(f.relative_to(pkg).with_suffix('').parts)
    except ValueError:
        return None


def lean_path(pkg: Path, tc: str) -> str:
    parts = [str(HOME / 'nt' / tc / '.lake/build/lib/lean'), str(pkg / '.lake/build/lib/lean')]
    for d in sorted((pkg / '.lake/packages').glob('*/.lake/build/lib/lean')):
        parts.append(str(d))
    return ':'.join(parts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name'); ap.add_argument('pkg')
    ap.add_argument('--jobs', type=int, default=32)
    ap.add_argument('--fact-timeout', type=int, default=900)
    ap.add_argument('--fact-mem', type=int, default=48)
    ap.add_argument('--split', type=int, default=8)
    ap.add_argument('--build-timeout', type=int, default=10800)
    ap.add_argument('--skip-build', action='store_true')
    ap.add_argument('--build-threads', type=int, default=16)
    a = ap.parse_args()
    pkg = Path(a.pkg).resolve(); tc = toolchain_of(pkg); env = env_for(tc)
    lean = ELAN / 'toolchains' / f"leanprover--lean4---{tc}" / 'bin' / 'lean'
    w = WORK / a.name; w.mkdir(parents=True, exist_ok=True); RESULTS.mkdir(exist_ok=True)
    log = w / 'driver.log'
    out = RESULTS / f"{a.name}.tsv"
    files = native_files(pkg)
    roots = src_dirs(pkg)
    mods = sorted({m for m in (module_of(f, pkg, roots) for f in files) if m})
    with open(log, 'a') as f:
        f.write(f"pkg={pkg} tc={tc} native_files={len(files)} modules={len(mods)}\n")
    if not (HOME / 'nt' / tc / '.lake/build/lib/lean/NativeTrust.olean').exists():
        print(f"no NativeTrust build for {tc}", file=sys.stderr); sys.exit(2)
    # 1-2. cache + targeted build (modules that fail to build are recorded, the rest continue)
    built = set()
    if not a.skip_build:
        if 'mathlib' in (pkg / 'lake-manifest.json').read_text(errors='ignore').lower() if (pkg / 'lake-manifest.json').exists() else False:
            run(['lake', 'exe', 'cache', 'get'], pkg, env, 3600, 64, w / 'cache.log')
        # Lake's job parallelism follows LEAN_NUM_THREADS: 16 concurrent Lean processes per build
        benv = dict(env); benv['LEAN_NUM_THREADS'] = str(a.build_threads)
        if mods:  # never a bare `lake build` (that builds every default target)
            run(['lake', 'build'] + mods, pkg, benv, a.build_timeout, 400, w / 'build.log')
    def has_olean(m):
        return (pkg / '.lake/build/lib/lean' / (m.replace('.', '/') + '.olean')).exists()
    if not a.skip_build:
        # a module outside every library makes a bulk `lake build` fail early: retry the missing ones alone
        for m in [m for m in mods if not has_olean(m)]:
            run(['lake', 'build', m], pkg, benv, a.build_timeout, 400, w / 'build_single.log')
    for m in mods:
        if has_olean(m):
            built.add(m)
    with open(out, 'a') as f:
        for m in mods:
            if m not in built:
                f.write(f"{a.name}\t{m}\t-\tNOT_BUILT\t\t\t\n")
    # 3. theorems per built module
    lp = lean_path(pkg, tc); env['LEAN_PATH'] = lp
    def list_thms(m):
        lf = w / f"list_{m}.lean"; lf.write_text(f"import NativeTrust\nimport {m}\n#native_theorems {m}\n")
        lg = w / f"list_{m}.log"
        run([lean, '-j1', lf], w, env, 1800, 64, lg)
        return [(m, l.split('\t')[1], int(l.split('\t')[2])) for l in lg.read_text(errors='ignore').splitlines()
                if l.startswith('THM\t')]
    thms = []
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        for r in ex.map(list_thms, sorted(built)):
            thms += r
    direct = [(m, t) for (m, t, d) in thms if d > 0]
    with open(log, 'a') as f:
        f.write(f"native theorems={len(thms)} direct facts={len(direct)}\n")
    # 4. one process per fact
    def check(mt):
        m, t = mt
        safe = re.sub(r'[^A-Za-z0-9_.]', '_', t)[:150]
        cf_ = w / f"chk_{safe}.lean"
        cf_.write_text(f"import NativeTrust\nimport {m}\nset_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"
                       f"#kernel_blockers {t}\ntrust_check {t} (config := {{ split := {a.split} }})\n")
        lg = w / f"chk_{safe}.log"
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
        line = f"{a.name}\t{m}\t{t}\t{verdict}\t{reason}\t{kms.group(1) if kms else ''}\t{rss.group(1) if rss else ''}\t{secs:.0f}\t{blockers}\n"
        with open(out, 'a') as f:
            f.write(line)
        return verdict
    with cf.ThreadPoolExecutor(a.jobs) as ex:
        verdicts = list(ex.map(check, direct))
    with open(log, 'a') as f:
        f.write('summary ' + ' '.join(f"{v}={verdicts.count(v)}" for v in sorted(set(verdicts))) + '\n')
    print(a.name, len(direct), 'facts:', {v: verdicts.count(v) for v in set(verdicts)})


if __name__ == '__main__':
    main()
