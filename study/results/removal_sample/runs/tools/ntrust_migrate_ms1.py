#!/usr/bin/env python3
"""ntrust migrate: replace `native_decide` / `decide +native` by `decide +kernel` wherever Lean's kernel checks
the fact, in a COPY of a Lake package; verify that the copy builds and that the rewritten declarations no longer
depend on native axioms; measure the build cost before and after. Run as the unprivileged build user.

usage: ntrust_migrate.py NAME PKG_DIR [--plain-results R] [--study-results R] [--jobs J] [--work DIR]
                         [--no-unknown] [--max-rounds N] [--build-timeout S] [--skip-default-build] [--phase P]

Pipeline (state in WORK/NAME/, the copy in WORK/NAME/pkg; PKG_DIR is only read):
 1. copy     cp -a PKG_DIR (with .lake, so dependencies are not rebuilt).
 2. census   a core-Lean script (Census.lean.in) per batch of built package modules: every native axiom
             `<decl>._native.<tactic>.ax_…` with its declaration range (Lean records the range of the tactic
             call, so each fact maps to one source occurrence), and every declaration whose dependency closure
             contains a native axiom.
 3. plan     lex the sources (comments and strings skipped) for `native_decide`, `decide +native` and
             `decide (config := { native := true })`; map facts to occurrences by range; an occurrence is
             rewritten when every fact it produced converted with plain kernel evaluation in the per-fact
             results (RESULTS/<R>.ax.tsv, verdict PROVED with `wf := false, split := 1`). Occurrences that
             produced no fact in the oleans (e.g. inside `example`) are tried too (the build decides) unless
             --no-unknown; occurrences inside macro/syntax definitions and `bv_decide` are never touched.
 4. time0    clean rebuild of the affected modules (their artifacts are deleted, then `lake build` them) on
             the original sources: wall, user+sys CPU, peak concurrency of `lean` processes.
 5. rewrite  apply the plan to the copy.
 6. build    `lake build` the affected modules; errors are attributed to occurrences (same line/column span,
             else same line, else enclosing declaration) and those occurrences are reverted; repeat.
 7. time1    the same clean rebuild as time0 on the rewritten sources.
 8. verify   `lake build` of the default targets (unless --skip-default-build), census after, comparison:
             native axioms and native-dependent declarations before/after, and for every rewritten
             declaration whether it still depends on a native axiom (and why).
 9. patch    unified diff against PKG_DIR (WORK/NAME/NAME.patch) and summary (WORK/NAME/summary.json).
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import argparse, concurrent.futures as cf, json, os, re, signal, subprocess, sys, threading, time
from pathlib import Path

HOME = Path(NT_BOX)
ELAN = HOME / 'elan'
RESULTS = HOME / 'results'
MIGRATE_ROOT = HOME / 'runs' / 'mig'  # the work root of the random-sample runs
HERE = Path(__file__).resolve().parent
NATIVE_RE = re.compile(r'native_decide|native\s*:=\s*true|\+native')
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*$")
CHAR_RE = re.compile(r"'(?:\\(?:x[0-9a-fA-F]{2}|u[0-9a-fA-F]{4}|.)|[^'\\\n])'")
DECIDE_CFG_RE = re.compile(r"decide((?:[ \t]*(?:[+-][A-Za-z_][A-Za-z0-9_]*|\((?:config[ \t]*:=[ \t]*\{[^{}()]*\}|[A-Za-z_][A-Za-z0-9_]*[ \t]*:=[^()]*)\)))*)")
MACRO_CMD_RE = re.compile(r"^(?:@\[[^\]]*\]\s*)?(?:(?:private|protected|scoped|local|noncomputable|partial|unsafe)\s+)*"
                          r"(?:macro|macro_rules|syntax|elab|elab_rules|notation|infix|infixl|infixr|prefix|postfix|"
                          r"meta|initialize|builtin_initialize)\b")
ERR_RE = re.compile(r'^error: (.+?\.lean):(\d+):(\d+): (.*)$')
BUILT_RE = re.compile(r'Built (\S+) \(([\d.]+)(m?s)\)')


def log(w, msg):
    line = f"{time.strftime('%FT%TZ', time.gmtime())} {msg}"
    print(line, flush=True)
    with open(w / 'migrate.log', 'a') as f:
        f.write(line + '\n')


def toolchain_of(pkg: Path) -> str:
    return (pkg / 'lean-toolchain').read_text().strip().split(':')[-1]


def env_for() -> dict:
    e = dict(os.environ)
    e['ELAN_HOME'] = str(ELAN)
    e['PATH'] = f"{ELAN}/bin:" + e.get('PATH', '/usr/bin:/bin')
    e.pop('LEAN_PATH', None)
    return e


RSS_CAP_GB = 44      # a `lean` process of a build above this resident size stops the build (memory budget)
BUILD_VMEM_GB = 128  # address-space cap of builds: Lean 4.31+ reserves ~1.2 GB of address space per elaboration
                     # thread (one per theorem with Elab.async); measured VmPeak 51 GB at 6.8 GB resident on
                     # Humanfia, so a 48 GB `ulimit -v` makes thread creation fail at random


def run(cmd, cwd, env, timeout, mem_gb, logf, sampler_root=None):
    """Run under `ulimit -v` and a time limit (coreutils timeout on the process group); return (rc, secs, out,
    max_lean) where max_lean is the peak number of concurrent `lean` processes whose cwd is under
    sampler_root (sampled every 0.5 s)."""
    t0 = time.time()
    peak = [0]
    stop = threading.Event()

    seen = {}
    rss = dict(peak_one=0, peak_sum=0, killed=False, killer=None)

    def sample():
        root = str(sampler_root)
        while not stop.is_set():
            n = 0
            tot = 0
            now = time.time() - t0
            for pid in os.listdir('/proc'):
                if not pid.isdigit():
                    continue
                try:
                    if open(f'/proc/{pid}/comm').read().strip() != 'lean':
                        continue
                    if os.readlink(f'/proc/{pid}/cwd').startswith(root):
                        n += 1
                        argv = open(f'/proc/{pid}/cmdline', 'rb').read().split(b'\0')
                        src = next((x.decode(errors='replace') for x in argv[1:] if x.endswith(b'.lean')), None)
                        if src:
                            fs = seen.setdefault(src, [now, now])
                            fs[1] = now
                        m = re.search(r'VmRSS:\s+(\d+) kB', open(f'/proc/{pid}/status').read())
                        if m:
                            kb = int(m.group(1))
                            tot += kb
                            rss['peak_one'] = max(rss['peak_one'], kb)
                            if kb > RSS_CAP_GB * 1048576 and not rss['killed']:
                                rss['killed'] = True
                                rss['killer'] = src
                                try:
                                    os.killpg(p.pid, signal.SIGTERM)
                                except (OSError, NameError):
                                    pass
                except OSError:
                    pass
            peak[0] = max(peak[0], n)
            rss['peak_sum'] = max(rss['peak_sum'], tot)
            stop.wait(0.5)
    th = None
    with open(logf, 'a') as f:
        f.write(f"$ {' '.join(map(str, cmd))}\n")
        f.flush()
        p = subprocess.Popen(['bash', '-c', f'ulimit -n 65536 2>/dev/null || ulimit -n $(ulimit -Hn); ulimit -v {mem_gb * 1024 * 1024}; '
                              f'exec timeout -k 30 {timeout} "$@"', 'cap'] + [str(c) for c in cmd],
                             cwd=cwd, env=env, stdout=subprocess.PIPE, stderr=subprocess.STDOUT, start_new_session=True)
        if sampler_root:
            th = threading.Thread(target=sample, daemon=True)
            th.start()
        chunks = []
        for line in iter(p.stdout.readline, b''):
            s = line.decode(errors='replace')
            chunks.append(s)
            f.write(s)
        try:
            rc = p.wait(timeout=120)
        except subprocess.TimeoutExpired:
            os.killpg(p.pid, signal.SIGKILL)
            p.wait()
            rc = 124
        f.write(f"rc={rc} secs={time.time() - t0:.0f}\n")
    stop.set()
    if th:
        th.join()
    run.last_seen = seen
    run.last_rss = rss
    if rss['killed']:
        with open(logf, 'a') as f:
            f.write(f"stopped: a lean process exceeded {RSS_CAP_GB} GB resident\n")
    return rc, time.time() - t0, ''.join(chunks), peak[0]


# ---------------------------------------------------------------- package layout (as m2_axioms5.py)

def src_dirs(pkg: Path):
    out = []
    for lf in ('lakefile.toml', 'lakefile.lean'):
        p = pkg / lf
        if p.exists():
            out += [pkg / m for m in re.findall(r'srcDir\s*(?::=|=)\s*"([^"]+)"', p.read_text())]
    return [d for d in out if d.resolve() != pkg.resolve()]


def lean_files(pkg: Path):
    out = []
    for f in pkg.rglob('*.lean'):
        rel = f.relative_to(pkg).parts
        if '.lake' in rel or 'lake-packages' in rel or rel[-1] in ('lakefile.lean',):
            continue
        out.append(f)
    return sorted(out)


def pkg_root_of(f: Path, pkg: Path) -> Path:
    d = f.parent
    while d != pkg and pkg in d.parents:
        if (d / 'lakefile.toml').exists() or (d / 'lakefile.lean').exists():
            return d
        d = d.parent
    return pkg


def module_of(f: Path, root: Path):
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
    return '.'.join(c if IDENT_RE.match(c) else f'«{c}»' for c in m.split('.'))


def lean_path(pkg: Path, env) -> list:
    p = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=pkg, env=env, capture_output=True, text=True,
                       timeout=900)
    parts = [x for x in p.stdout.strip().split(':') if x] if p.returncode == 0 else []
    if not parts:
        parts = [str(pkg / '.lake/build/lib/lean')] + [str(d) for d in sorted((pkg / '.lake/packages').glob('*/.lake/build/lib/lean'))]
    return parts


def olean_of(m: str, lp: list, under: Path):
    rel = Path(*m.split('.'))
    for d in lp:
        p = Path(d) / (str(rel) + '.olean')
        if p.exists() and str(Path(d).resolve()).startswith(str(under.resolve())):
            return p
    return None


# ---------------------------------------------------------------- lexing

def is_idc(ch: str) -> bool:
    return ch.isalnum() or ch in "_'!?" or ('₀' <= ch <= 'ₜ') or ('ᵢ' <= ch <= 'ᵪ')


def code_mask(text: str) -> bytearray:
    """1 at every character that is code (not in a comment, string or character literal)."""
    n = len(text)
    mask = bytearray(n)
    i = 0
    while i < n:
        c = text[i]
        if c == '-' and text.startswith('--', i):
            j = text.find('\n', i)
            i = n if j < 0 else j
            continue
        if c == '/' and text.startswith('/-', i):
            depth, j = 1, i + 2
            while j < n and depth:
                if text.startswith('/-', j):
                    depth += 1
                    j += 2
                elif text.startswith('-/', j):
                    depth -= 1
                    j += 2
                else:
                    j += 1
            i = j
            continue
        if c == '"':
            j = i + 1
            while j < n and text[j] != '"':
                j += 2 if text[j] == '\\' else 1
            i = j + 1
            continue
        if c == "'" and (i == 0 or not is_idc(text[i - 1])):
            m = CHAR_RE.match(text, i)
            if m:
                i = m.end()
                continue
        mask[i] = 1
        i += 1
    return mask


def line_starts(text: str):
    ls = [0]
    for i, ch in enumerate(text):
        if ch == '\n':
            ls.append(i + 1)
    return ls


def pos_of(ls, off):
    """(line 1-based, column 0-based in code points) of offset `off`."""
    lo, hi = 0, len(ls) - 1
    while lo < hi:
        mid = (lo + hi + 1) // 2
        if ls[mid] <= off:
            lo = mid
        else:
            hi = mid - 1
    return lo + 1, off - ls[lo]


def in_macro_context(text: str, ls, off: int) -> bool:
    """The occurrence lies in a macro/syntax/elab definition or a syntax quotation: rewriting it would change
    every use, and its facts are attributed to the use sites."""
    line, _ = pos_of(ls, off)
    k = line - 1
    while k > 0 and (k >= len(ls) or not text[ls[k]:ls[k] + 1].strip() or text[ls[k]] in ' \t'):
        k -= 1
    cmd = text[ls[k]:off]
    return bool(MACRO_CMD_RE.match(cmd)) or '`(' in cmd or '(tactic|' in cmd or '(tacticSeq|' in cmd


def occurrences(f: Path, pkg: Path):
    text = f.read_text(errors='replace')
    if not NATIVE_RE.search(text):
        return []
    mask = code_mask(text)
    ls = line_starts(text)
    out = []
    for m in re.finditer(r'native_decide', text):
        s, e = m.start(), m.end()
        if not mask[s]:
            continue
        prev = text[s - 1] if s else ' '
        nxt = text[e] if e < len(text) else ' '
        if is_idc(prev) or prev in '.`«' or is_idc(nxt):
            continue
        line, col = pos_of(ls, s)
        out.append(dict(file=str(f.relative_to(pkg)), start=s, end=e, line=line, col=col, kind='native_decide',
                        old='native_decide', new='decide +kernel', macro=in_macro_context(text, ls, s)))
    for m in DECIDE_CFG_RE.finditer(text):
        s, e = m.start(), m.end()
        if not mask[s]:
            continue
        prev = text[s - 1] if s else ' '
        if is_idc(prev) or prev in '.`«':
            continue
        cfg = m.group(1)
        if not cfg:
            continue
        new_cfg = None
        if re.search(r'\+native\b', cfg):
            new_cfg = re.sub(r'\+native\b', '+kernel', cfg)
            kind = 'decide +native'
        elif re.search(r'\bnative\s*:=\s*true\b', cfg):
            new_cfg = re.sub(r'\bnative(\s*):=(\s*)true\b', r'kernel\1:=\2true', cfg)
            kind = 'decide (native := true)'
        if new_cfg is None:
            continue
        line, col = pos_of(ls, s)
        out.append(dict(file=str(f.relative_to(pkg)), start=s, end=e, line=line, col=col, kind=kind,
                        old=text[s:e], new='decide' + new_cfg, macro=in_macro_context(text, ls, s)))
    out.sort(key=lambda o: o['start'])
    return out


# ---------------------------------------------------------------- census

def census(w: Path, tag: str, pkg: Path, lean: Path, env: dict, mods: list, jobs: int, batch: int = 40):
    """Run Census.lean.in over the modules in batches (a failing batch is split); returns dict with keys
    ax (list), dirty (list), mod (dict), failed (list)."""
    outdir = w / f'census_{tag}'
    outdir.mkdir(exist_ok=True)
    tmpl = (HERE / 'Census.lean.in').read_text()
    res = dict(ax=[], dirty=[], mod={}, failed=[])
    lock = threading.Lock()
    counter = [0]

    def one(b):
        with lock:
            k = counter[0]
            counter[0] += 1
        src = outdir / f'C{k}.lean'
        out = outdir / f'C{k}.tsv'
        lg = outdir / f'C{k}.log'
        for p in (out, lg):
            if p.exists():
                p.unlink()
        src.write_text(tmpl.replace('@@IMPORTS@@', ''.join(f'import {esc(m)}\n' for m in b))
                       .replace('@@OUT@@', str(out)).replace('@@MODS@@', ', '.join(f'`{esc(m)}' for m in b)))
        rc, secs, txt, _ = run([lean, '-j1', src], outdir, env, 3600, 48, lg)
        ok = out.exists() and out.read_text(errors='ignore').rstrip().endswith('END')
        if not ok:
            if len(b) > 1:
                h = len(b) // 2
                return one(b[:h]) + one(b[h:])
            with lock:
                res['failed'].append(b[0])
            return []
        return out.read_text(errors='ignore').splitlines()

    batches = [mods[i:i + batch] for i in range(0, len(mods), batch)]
    with cf.ThreadPoolExecutor(jobs) as ex:
        for lines in ex.map(one, batches):
            for l in lines:
                c = l.split('\t')
                if c[0] == 'AX' and len(c) >= 7:
                    res['ax'].append(dict(module=c[1], axiom=c[2], tactic=c[3], range=c[4], parent=c[5], prange=c[6]))
                elif c[0] == 'DIRTY' and len(c) >= 6:
                    res['dirty'].append(dict(module=c[1], decl=c[2], kind=c[3], parent=c[4], prange=c[5]))
                elif c[0] == 'MOD' and len(c) >= 6:
                    res['mod'][c[1]] = dict(n_ax=int(c[2]), n_user=int(c[3]), n_dirty=int(c[4]), capable=c[5] == '1')
    normalize_census(res)
    (w / f'census_{tag}.json').write_text(json.dumps(res))
    return res


def unesc(m: str) -> str:
    """Module name as Lean prints it (`A.«389»`) -> the dotted file-derived form used here (`A.389`)."""
    return m.replace('«', '').replace('»', '')


def normalize_census(res):
    """Census records with module names in the unescaped form (older census files printed `«…»`)."""
    for x in res['ax'] + res['dirty']:
        x['module'] = unesc(x['module'])
    res['mod'] = {unesc(k): v for k, v in res['mod'].items()}
    res['failed'] = [unesc(m) for m in res['failed']]
    return res


def parse_rng(s):
    if not s or s == '-':
        return None
    a = [int(x) for x in s.split(':')]
    return tuple(a) if len(a) == 4 else None


# ---------------------------------------------------------------- results

def load_results(name):
    out = {}
    if not name:
        return out
    f = RESULTS / f'{name}.ax.tsv'
    if not f.exists():
        return out
    for line in f.read_text(errors='ignore').splitlines():
        c = line.split('\t')
        if len(c) >= 7 and c[2] not in ('-', ''):
            try:
                secs = float(c[9]) if len(c) > 9 and c[9] else 0.0
            except ValueError:
                secs = 0.0
            out[c[2]] = dict(verdict=c[5], reason=c[6], blockers=c[10] if len(c) > 10 else '', secs=secs)
    return out


# ---------------------------------------------------------------- build functions

ART_LIB = ['.olean', '.ilean', '.trace', '.olean.hash', '.ilean.hash', '.olean.private', '.olean.server',
           '.olean.private.hash', '.olean.server.hash', '.ir', '.ir.hash', '.hash']
ART_IR = ['.c', '.c.hash', '.c.o', '.c.o.hash', '.c.o.trace', '.c.trace']


def delete_artifacts(w: Path, pkg: Path, lp: list, mods):
    """Delete the build artifacts (explicit files only) of `mods` in the copy's own build directories, so that
    `lake build` rebuilds exactly these modules."""
    pkg_r = str(pkg.resolve())
    assert pkg_r.startswith(str(MIGRATE_ROOT) + '/') and '/pkg' in pkg_r and str(w.resolve()) in pkg_r, pkg_r
    n = 0
    for m in mods:
        o = olean_of(m, lp, pkg)
        if not o:
            continue
        rel = Path(*m.split('.'))
        libdir = Path(str(o)[:-len(str(rel) + '.olean')])
        builddir = libdir.parent.parent
        cands = [libdir / (str(rel) + e) for e in ART_LIB] + [builddir / 'ir' / (str(rel) + e) for e in ART_IR]
        for p in cands:
            rp = str(p.resolve()) if p.exists() else ''
            if rp and rp.startswith(pkg_r + '/') and '/.lake/' in rp and p.is_file():
                p.unlink()
                n += 1
    return n


def lake_build(w, pkg, env, targets, tag, jobs, timeout):
    benv = dict(env)
    benv['LEAN_NUM_THREADS'] = str(jobs)
    lg = w / f'build_{tag}.log'
    if lg.exists():
        lg.unlink()
    cmd = ['/usr/bin/time', '-f', 'TIME wall=%e user=%U sys=%S maxrss_kb=%M', 'lake', 'build', '--no-ansi'] + ['+' + esc(t) for t in targets]
    rc, secs, out, peak = run(cmd, pkg, benv, timeout, BUILD_VMEM_GB, lg, sampler_root=pkg)
    rss = getattr(run, 'last_rss', {})
    tm = re.search(r'TIME wall=([\d.]+) user=([\d.]+) sys=([\d.]+) maxrss_kb=(\d+)', out)
    built = {}
    for m in BUILT_RE.finditer(out):
        v = float(m.group(2)) * (0.001 if m.group(3) == 'ms' else 1)
        built[m.group(1)] = v
    errs = []
    for l in out.splitlines():
        m = ERR_RE.match(l.strip())
        if m:
            p = (pkg / m.group(1)).resolve()
            try:
                rel = str(p.relative_to(pkg.resolve()))
            except ValueError:
                rel = m.group(1)
            errs.append(dict(file=rel, line=int(m.group(2)), col=int(m.group(3)), msg=m.group(4)[:300]))
    failed_mods = sorted(set(re.findall(r'✖ \[\d+/\d+\] Building (\S+)', out)) |
                         set(re.findall(r'(?m)^- (\S+)$', out.split('Some required targets logged failures:')[-1])
                             if 'Some required targets logged failures:' in out else []))
    killer = None
    if rss.get('killer'):
        p = Path(rss['killer'])
        p = p if p.is_absolute() else pkg / p
        try:
            killer = str(p.resolve().relative_to(pkg.resolve()))
        except ValueError:
            killer = rss['killer']
    running = []
    if rc == 124:
        end = secs
        for src, (t_a, t_b) in getattr(run, 'last_seen', {}).items():
            if t_b >= end - 5:
                p = (pkg / src).resolve() if not src.startswith('/') else Path(src).resolve()
                try:
                    running.append(str(p.relative_to(pkg.resolve())))
                except ValueError:
                    running.append(src)
    return dict(rc=rc, secs=round(secs, 1), running=running, failed_mods=failed_mods, rss_killer=killer,
                thread_fail=out.count('failed to create thread'),
                peak_rss_gb=round(rss.get('peak_one', 0) / 1048576, 1),
                peak_rss_sum_gb=round(rss.get('peak_sum', 0) / 1048576, 1), rss_killed=rss.get('killed', False),
                wall=float(tm.group(1)) if tm else None,
                cpu=round(float(tm.group(2)) + float(tm.group(3)), 1) if tm else None,
                maxrss_kb=int(tm.group(4)) if tm else None, peak_lean=peak, built=built, errors=errs,
                n_built=len(built), tail=out[-3000:] if rc else '')


# ---------------------------------------------------------------- rewriting

def apply_rewrites(pkg: Path, orig: Path, occs_by_file: dict, active: set, bumps=None, bump_text=''):
    """Write every file from its ORIGINAL text with the active occurrences replaced and `bump_text` inserted at
    the declaration starts in `bumps` (rel -> {(line, col): occurrence ids}); record the occurrences' new
    column spans (line numbers never change: replacements and insertions contain no newline)."""
    bumps = bumps or {}
    for rel, occs in occs_by_file.items():
        src = (orig / rel).read_text(errors='replace')
        ls = line_starts(src)
        edits = []  # (offset, end, new, occurrence or None)
        for o in occs:
            edits.append((o['start'], o['end'], o['new'] if o['id'] in active else o['old'], o))
        for (line, col) in bumps.get(rel, {}):
            off = ls[line - 1] + col
            edits.append((off, off, bump_text, None))
        edits.sort(key=lambda e: (e[0], e[3] is not None))
        pieces, last = [], 0
        delta_by_line = {}
        for (a, b, new, o) in edits:
            pieces.append(src[last:a])
            pieces.append(new)
            last = b
            line, col = pos_of(ls, a)
            d = delta_by_line.get(line, 0)
            if o is not None:
                o['new_col'] = o['col'] + d
                o['new_end'] = o['new_col'] + len(new)
            delta_by_line[line] = d + len(new) - (b - a)
        pieces.append(src[last:])
        new_text = ''.join(pieces)
        target = pkg / rel
        if target.read_text(errors='replace') != new_text:
            target.write_text(new_text)


HEARTBEAT_RE = re.compile(r'maximum number of heartbeats|deterministic\) timeout')


def decl_start(pkg: Path, rel: str, line: int, decl_ranges):
    """(line, col) where the declaration containing `line` starts: the census range of the smallest enclosing
    declaration, else (examples) the last command line at column 0 at or above `line`, moved up over a doc
    comment that ends right above it."""
    for (l1, c1, l2) in decl_ranges.get(rel, []):
        if l1 <= line <= l2:
            return (l1, c1), (l1, l2)
    lines = (pkg / rel).read_text(errors='replace').split('\n')
    k = min(line, len(lines))
    while k > 1 and (not lines[k - 1].strip() or lines[k - 1][0] in ' \t' or lines[k - 1].startswith('--')):
        k -= 1
    if k > 1 and lines[k - 2].rstrip().endswith('-/'):
        j = k - 1
        while j > 1 and not lines[j - 1].startswith('/-'):
            j -= 1
        if lines[j - 1].startswith('/--'):
            k = j
    e = line
    while e < len(lines) and (not lines[e].strip() or lines[e][0] in ' \t'):
        e += 1
    return (k, 0), (k, e)


def attribute(errors, occs_by_file, active, decl_ranges, pkg=None, bumps=None, bump_on=False):
    """Occurrences to revert for a list of build errors: same line and column span, else the occurrence that
    starts right after the error position on that line (`by` before the tactic), else the active
    occurrences on that line, else the active occurrences in the enclosing declaration, else all active
    occurrences of the file. With bump_on, a heartbeat error in a declaration that has no bump yet adds one
    instead (returned in new_bumps: rel -> {(line, col): ids})."""
    hit, unattributed, new_bumps = {}, [], {}
    for e in errors:
        occs = [o for o in occs_by_file.get(e['file'], []) if o['id'] in active]
        if not occs:
            unattributed.append(e)
            continue
        if bump_on and HEARTBEAT_RE.search(e['msg']) and pkg is not None:
            start, (l1, l2) = decl_start(pkg, e['file'], e['line'], decl_ranges)
            if start not in (bumps or {}).get(e['file'], {}) and start not in new_bumps.get(e['file'], {}):
                ids = {o['id'] for o in occs if l1 <= o['line'] <= l2}
                if ids:
                    new_bumps.setdefault(e['file'], {})[start] = ids
                    continue
        c = [o for o in occs if o['line'] == e['line'] and o['new_col'] <= e['col'] < o['new_end']]
        if not c:
            after = [o for o in occs if o['line'] == e['line'] and 0 <= o['new_col'] - e['col'] <= 3]
            c = after[:1]
        if not c:
            c = [o for o in occs if o['line'] == e['line']]
        if not c:
            for (l1, c1, l2) in decl_ranges.get(e['file'], []):
                if l1 <= e['line'] <= l2:
                    c = [o for o in occs if l1 <= o['line'] <= l2]
                    if c:
                        break
        if not c:
            c = occs
        for o in c:
            hit.setdefault(o['id'], e['msg'])
    return hit, unattributed, new_bumps


# ---------------------------------------------------------------- main

def main():
    ap = argparse.ArgumentParser()
    ap.add_argument('name')
    ap.add_argument('pkg')
    ap.add_argument('--plain-results', default=None, help='per-fact results with plain kernel evaluation (default NAME-plain)')
    ap.add_argument('--study-results', default=None, help='per-fact results of the study run (default NAME), for reasons')
    ap.add_argument('--jobs', type=int, default=8)
    ap.add_argument('--work', default=str(MIGRATE_ROOT))
    ap.add_argument('--copy-root', default=None, help='copy this ancestor of PKG_DIR (for path dependencies such as ../core)')
    ap.add_argument('--no-unknown', action='store_true', help='do not try occurrences that left no fact in the oleans')
    ap.add_argument('--max-rounds', type=int, default=5)
    ap.add_argument('--build-timeout', type=int, default=7200)
    ap.add_argument('--round-timeout', type=int, default=900, help='time limit of one build round of the rewrite loop')
    ap.add_argument('--max-fact-seconds', type=float, default=None,
                    help='keep occurrences with a fact whose per-fact check took longer than this (build cost)')
    ap.add_argument('--bump-heartbeats', type=int, default=None,
                    help='opt-in: when a declaration exceeds maxHeartbeats after the rewrite, prefix it with '
                         '`set_option maxHeartbeats N in` instead of reverting (0 = no limit)')
    ap.add_argument('--skip-default-build', action='store_true')
    ap.add_argument('--skip-timing', action='store_true')
    ap.add_argument('--census-batch', type=int, default=40)
    ap.add_argument('--phase', default='all', help='stop after this phase (census, plan, time0, build, time1, verify)')
    a = ap.parse_args()

    orig = Path(a.pkg).resolve()
    w = Path(a.work) / a.name
    w.mkdir(parents=True, exist_ok=True)
    root = Path(a.copy_root).resolve() if a.copy_root else orig
    sub = orig.relative_to(root)  # ValueError if --copy-root is not an ancestor of PKG_DIR
    pkg = w / 'pkg' / sub
    plain_name = a.plain_results if a.plain_results is not None else f'{a.name}-plain'
    study_name = a.study_results if a.study_results is not None else a.name
    env = env_for()
    if not (w / 'pkg').exists():
        log(w, f'copy {root} -> {w / "pkg"}')
        subprocess.run(['cp', '-a', str(root), str(w / 'pkg')], check=True)
    tc = toolchain_of(pkg)
    lean = ELAN / 'toolchains' / f"leanprover--lean4---{tc}" / 'bin' / 'lean'
    if not lean.exists():
        lean = ELAN / 'toolchains' / f"leanprover--lean4-nightly---{tc}" / 'bin' / 'lean'
    state_f = w / 'state.json'
    st = json.loads(state_f.read_text()) if state_f.exists() else {}

    def save():
        state_f.write_text(json.dumps(st, indent=1))

    if a.phase == 'report':
        write_report(w, a.name, orig, pkg, tc, st)
        return
    if a.phase == 'verify':
        # the verification build alone (every module of the census), then the report again
        c0 = normalize_census(json.loads((w / 'census_before.json').read_text()))
        built = sorted(set(c0['mod']) | set(c0['failed']))
        bd = lake_build(w, pkg, env, built, 'default', a.jobs, a.build_timeout)
        st['default_build'] = {k: bd[k] for k in ('rc', 'wall', 'cpu', 'n_built', 'peak_lean', 'peak_rss_gb', 'peak_rss_sum_gb')}
        st['default_build']['errors'] = bd['errors'][:20]
        save()
        log(w, f"default build: rc={bd['rc']} wall={bd['wall']} built={bd['n_built']} errors={len(bd['errors'])}")
        write_report(w, a.name, orig, pkg, tc, st)
        return
    if a.phase == 'census-after':
        # census after and report again from the saved final plan (e.g. when the first census after missed
        # modules that were rebuilt later)
        c0 = normalize_census(json.loads((w / 'census_before.json').read_text()))
        lp = lean_path(pkg, env)
        cenv = dict(env, LEAN_PATH=':'.join(lp), LEAN_NUM_THREADS='1')
        census(w, 'after', pkg, lean, cenv, sorted(set(c0['mod']) | set(c0['failed'])), a.jobs, a.census_batch)
        write_report(w, a.name, orig, pkg, tc, st)
        return
    if a.phase == 'census-after-noreverts':
        # recovery for a run stopped after its build rounds when no occurrence was reverted (all planned
        # rewrites are in the copy): mark them replaced, census after, report
        assert st.get('rounds') and st['rounds'][-1]['rc'] == 0 and not any(r['reverted'] for r in st['rounds'])
        d = json.loads((w / 'plan.json').read_text())
        for o in d['occs']:
            if o['status'] in ('rewrite', 'try'):
                o['status'] = 'replaced'
        (w / 'plan.json').write_text(json.dumps(d, indent=0))
        c0 = normalize_census(json.loads((w / 'census_before.json').read_text()))
        lp = lean_path(pkg, env)
        cenv = dict(env, LEAN_PATH=':'.join(lp), LEAN_NUM_THREADS='1')
        census(w, 'after', pkg, lean, cenv, sorted(set(c0['mod']) | set(c0['failed'])), a.jobs, a.census_batch)
        write_report(w, a.name, orig, pkg, tc, st)
        return
    lp = lean_path(pkg, env)
    cenv = dict(env)
    cenv['LEAN_PATH'] = ':'.join(lp)
    cenv['LEAN_NUM_THREADS'] = '1'
    files = lean_files(pkg)
    modfile, filemod = {}, {}
    for f in files:
        m = module_of(f, pkg_root_of(f, pkg))
        if m:
            rel = str(f.relative_to(pkg))
            modfile[m] = rel
            filemod[rel] = m
    built = sorted(m for m in modfile if olean_of(m, lp, pkg))
    log(w, f'{a.name}: tc={tc} files={len(files)} modules={len(modfile)} built={len(built)} plain={plain_name} study={study_name}')

    # 2. census before
    if 'census0' not in st:
        t0 = time.time()
        c0 = census(w, 'before', pkg, lean, cenv, built, a.jobs, a.census_batch)
        st['census0'] = dict(secs=round(time.time() - t0), failed=c0['failed'])
        save()
    c0 = normalize_census(json.loads((w / 'census_before.json').read_text()))
    # the modules that were built when the copy was made (the census covered exactly these): the plan, the
    # final verification build and the comparison refer to this set, whatever later runs did to the copy
    built = sorted(set(c0['mod']) | set(c0['failed']))
    log(w, f"census before: {len(c0['ax'])} native axioms, {len(c0['dirty'])} native-dependent declarations, modules={len(built)}, failed={c0['failed']}")
    if a.phase == 'census':
        return

    # 3. plan
    occs, occs_by_file = [], {}
    for f in files:
        rel = str(f.relative_to(pkg))
        of = occurrences((orig / rel) if (orig / rel).exists() else f, orig if (orig / rel).exists() else pkg)
        for o in of:
            o['file'] = rel
            o['id'] = len(occs)
            o['module'] = filemod.get(rel)
            occs.append(o)
        if of:
            occs_by_file[rel] = of
    by_pos = {(o['file'], o['line'], o['col']): o for o in occs}
    plain = load_results(plain_name)
    study = load_results(study_name)
    unmatched = []
    for x in c0['ax']:
        r = parse_rng(x['range'])
        rel = modfile.get(x['module'])
        o = by_pos.get((rel, r[0], r[1])) if (r and rel) else None
        if o is None:
            unmatched.append(x)
            continue
        o.setdefault('facts', []).append(x['axiom'])
    decl_ranges = {}
    for x in c0['ax'] + c0['dirty']:
        r = parse_rng(x['prange'])
        rel = modfile.get(x['module'])
        if r and rel:
            decl_ranges.setdefault(rel, set()).add((r[0], r[1], r[2]))
    decl_ranges = {k: sorted(v, key=lambda t: t[2] - t[0]) for k, v in decl_ranges.items()}
    builtset = set(built)
    for o in occs:
        facts = o.get('facts', [])
        o['status'], o['reason'] = 'rewrite', ''
        if o['macro']:
            o['status'], o['reason'] = 'keep', 'inside a macro/syntax definition'
        elif o['module'] not in builtset:
            o['status'], o['reason'] = 'keep', 'module not built'
        elif not facts:
            if a.no_unknown:
                o['status'], o['reason'] = 'keep', 'no fact in the olean (example?)'
            else:
                o['status'], o['reason'] = 'try', 'no fact in the olean (example?): the build decides'
        else:
            bad = []
            for ax in facts:
                p = plain.get(ax)
                if p and p['verdict'] == 'PROVED':
                    continue
                s = study.get(ax)
                if p:
                    bad.append(f"plain {p['verdict']}/{p['reason']}" + (f" ({p['blockers'][:60]})" if p['blockers'] else ''))
                elif s and s['verdict'] != 'PROVED':
                    bad.append(f"{s['verdict']}/{s['reason']}" + (f" ({s['blockers'][:60]})" if s['blockers'] else ''))
                elif s:
                    bad.append('proved only with transformations? (no plain result)')
                else:
                    bad.append('no per-fact result')
            if not bad and a.max_fact_seconds is not None:
                slow = max(plain[ax]['secs'] for ax in facts)
                if slow > a.max_fact_seconds:
                    bad.append(f'kernel evaluation took {slow:.0f} s for one fact (per-fact result; limit {a.max_fact_seconds} s)')
            if bad:
                o['status'], o['reason'] = 'keep', bad[0] + (f' (+{len(bad) - 1} more facts)' if len(bad) > 1 else '')
    affected = sorted({o['module'] for o in occs if o['status'] in ('rewrite', 'try')})
    plan = dict(n_occ=len(occs), affected=affected, unmatched=unmatched[:200], n_unmatched=len(unmatched),
                counts={})
    for o in occs:
        k = o['status'] + (': ' + o['reason'] if o['status'] == 'keep' else '')
        plan['counts'][k] = plan['counts'].get(k, 0) + 1
    (w / 'plan.json').write_text(json.dumps(dict(plan=plan, occs=occs), indent=0))
    log(w, f"plan: {len(occs)} occurrences; {json.dumps(plan['counts'])}; unmatched axioms={len(unmatched)}; affected modules={len(affected)}")
    if a.phase == 'plan':
        return

    # 4. time0: clean rebuild of the affected modules on the original sources
    for o in occs:
        o['active'] = False
    apply_rewrites(pkg, orig, occs_by_file, set())
    if not a.skip_timing and 'time0' not in st:
        n = delete_artifacts(w, pkg, lp, affected)
        b0 = lake_build(w, pkg, env, affected, 'time0', a.jobs, a.build_timeout)
        b0['deleted'] = n
        st['time0'] = b0
        save()
        log(w, f"time0: rc={b0['rc']} wall={b0['wall']} cpu={b0['cpu']} built={b0['n_built']} peak_lean={b0['peak_lean']} peak_rss_gb={b0['peak_rss_gb']} sum={b0['peak_rss_sum_gb']} errors={len(b0['errors'])}")
    if a.phase == 'time0':
        return
    orig_err_files = {e['file'] for e in st.get('time0', {}).get('errors', [])}

    # 5./6. rewrite + build loop
    active = {o['id'] for o in occs if o['status'] in ('rewrite', 'try') and o['file'] not in orig_err_files}
    for o in occs:
        if o['status'] in ('rewrite', 'try') and o['file'] in orig_err_files:
            o['status'], o['reason'] = 'keep', 'the original module does not build'
    rounds = []
    reverted = {}
    # a round rebuilds the affected modules like time0 did, plus the kernel work: never stop it before twice
    # the original clean rebuild time (+10 min)
    t0w = (st.get('time0') or {}).get('wall') or 0
    round_timeout = max(a.round_timeout, int(2 * t0w) + 600)
    if round_timeout != a.round_timeout:
        log(w, f'round timeout raised to {round_timeout} s (time0 wall {t0w} s)')
    bump_on = a.bump_heartbeats is not None
    bump_text = f'set_option maxHeartbeats {a.bump_heartbeats} in ' if bump_on else ''
    bumps = {}  # rel -> {(line, col): occurrence ids of the declaration}

    def prune_bumps():
        for rel in list(bumps):
            for k in [k for k, ids in bumps[rel].items() if not (ids & active)]:
                del bumps[rel][k]
            if not bumps[rel]:
                del bumps[rel]
    for rnd in range(a.max_rounds):
        apply_rewrites(pkg, orig, occs_by_file, active, bumps, bump_text)
        targets = sorted({o['module'] for o in occs if o['id'] in active}) or affected
        b = lake_build(w, pkg, env, targets, f'round{rnd}', a.jobs, round_timeout)
        for attempt in range(2):
            # a `lean` that could not create a thread (address-space cap) is an environment failure, not a
            # verdict: build again (finished modules are not rebuilt)
            if b['rc'] == 0 or not b['thread_fail'] or b['errors']:
                break
            log(w, f"round {rnd}: {b['thread_fail']} 'failed to create thread'; building again")
            b = lake_build(w, pkg, env, targets, f'round{rnd}_retry{attempt}', a.jobs, round_timeout)
        hit, unattr, new_bumps = attribute(b['errors'], occs_by_file, active, decl_ranges, pkg, bumps, bump_on)
        for rel, d in new_bumps.items():
            bumps.setdefault(rel, {}).update(d)
        if b['rss_killed'] and b['rss_killer']:
            # a module whose elaboration exceeded the resident-memory cap: revert its occurrences
            for o in occs_by_file.get(b['rss_killer'], []):
                if o['id'] in active:
                    hit.setdefault(o['id'], f'module elaboration exceeded {RSS_CAP_GB} GB resident')
            log(w, f"round {rnd}: {b['rss_killer']} exceeded {RSS_CAP_GB} GB resident; build stopped")
        if b['rc'] == 124:
            # modules still elaborating at the round's time limit: revert their untested occurrences
            # (no per-fact result) first; if they have none, all their occurrences
            for rel in b['running']:
                act = [o for o in occs_by_file.get(rel, []) if o['id'] in active]
                tried = [o for o in act if o['status'] == 'try']
                for o in (tried or act):
                    hit.setdefault(o['id'], f"build of the module exceeded {round_timeout} s")
            log(w, f"round {rnd} timed out; still running: {b['running']}")
        n_new_bumps = sum(len(d) for d in new_bumps.values())
        rounds.append(dict(round=rnd, rc=b['rc'], wall=b['wall'], cpu=b['cpu'], n_errors=len(b['errors']),
                           reverted=len(hit), bumped=n_new_bumps, unattributed=unattr[:20], peak_lean=b['peak_lean'],
                           peak_rss_gb=b['peak_rss_gb'], rss_killed=b['rss_killed']))
        log(w, f"build round {rnd}: rc={b['rc']} wall={b['wall']} errors={len(b['errors'])} revert={len(hit)} bump={n_new_bumps} unattributed={len(unattr)} peak_lean={b['peak_lean']} peak_rss_gb={b['peak_rss_gb']}")
        if b['rc'] == 0:
            break
        if not hit and n_new_bumps:
            continue
        if not hit:
            log(w, f"build failed without attributable errors (failed modules {b['failed_mods']}); tail:\n" + b['tail'][-1500:])
            # revert the occurrences of the modules that failed (all target modules if none was named)
            failed = set(b['failed_mods']) or set(targets)
            for o in occs:
                if o['id'] in active and o['module'] in failed:
                    hit[o['id']] = 'unattributed build failure of the module'
        for i, msg in hit.items():
            active.discard(i)
            reverted[i] = msg
        prune_bumps()
        st['rounds'] = rounds
        save()
    else:
        prune_bumps()
        apply_rewrites(pkg, orig, occs_by_file, active, bumps, bump_text)
    st['rounds'] = rounds
    st['bumps'] = {rel: [list(k) for k in d] for rel, d in bumps.items()}
    final_ok = bool(rounds) and rounds[-1]['rc'] == 0
    bumped_ids = set()
    for d in bumps.values():
        for ids in d.values():
            bumped_ids |= ids
    for o in occs:
        if o['id'] in reverted:
            o['status'], o['reason'] = 'keep', 'build: ' + reverted[o['id']]
        elif o['id'] in active:
            o['status'] = 'replaced'
            if o['id'] in bumped_ids:
                o['bumped'] = True
    save()
    if a.phase == 'build':
        (w / 'plan.json').write_text(json.dumps(dict(plan=plan, occs=occs), indent=0))
        return

    # 7. census after (first, so that the axiom comparison is available early), then time1, then the
    # verification build; the report is rewritten after each step
    st.pop('time1', None)
    st.pop('default_build', None)
    save()
    if final_ok:
        # modules whose occurrences were all reverted in a failed round have no olean yet: build them
        bs = lake_build(w, pkg, env, affected, 'settle', a.jobs, a.build_timeout)
        log(w, f"settle build of the affected modules: rc={bs['rc']} wall={bs['wall']}")
    c1 = census(w, 'after', pkg, lean, cenv, built, a.jobs, a.census_batch)
    (w / 'plan.json').write_text(json.dumps(dict(plan=plan, occs=occs), indent=0))
    write_report(w, a.name, orig, pkg, tc, st)
    if not a.skip_timing and final_ok:
        n = delete_artifacts(w, pkg, lp, affected)
        b1 = lake_build(w, pkg, env, affected, 'time1', a.jobs, a.build_timeout)
        b1['deleted'] = n
        st['time1'] = b1
        save()
        log(w, f"time1: rc={b1['rc']} wall={b1['wall']} cpu={b1['cpu']} built={b1['n_built']} peak_lean={b1['peak_lean']} peak_rss_gb={b1['peak_rss_gb']} sum={b1['peak_rss_sum_gb']} errors={len(b1['errors'])}")
        write_report(w, a.name, orig, pkg, tc, st)
    # 8. verify: build every module that was built in the original copy (the rewritten modules and everything
    # downstream of them are rebuilt)
    if not a.skip_default_build and final_ok:
        bd = lake_build(w, pkg, env, built, 'default', a.jobs, a.build_timeout)
        st['default_build'] = {k: bd[k] for k in ('rc', 'wall', 'cpu', 'n_built', 'peak_lean', 'peak_rss_gb', 'peak_rss_sum_gb')}
        st['default_build']['errors'] = bd['errors'][:20]
        save()
        log(w, f"default build: rc={bd['rc']} wall={bd['wall']} built={bd['n_built']} errors={len(bd['errors'])}")
        write_report(w, a.name, orig, pkg, tc, st)


def write_report(w, name, orig, pkg, tc, st):
    """Summary (summary.json), patch (NAME.patch) and log line from the saved plan, census and state files
    (also usable alone: --phase report)."""
    d = json.loads((w / 'plan.json').read_text())
    plan, occs = d['plan'], d['occs']
    c0 = normalize_census(json.loads((w / 'census_before.json').read_text()))
    c1 = normalize_census(json.loads((w / 'census_after.json').read_text()))
    occs_by_file = {}
    for o in occs:
        occs_by_file.setdefault(o['file'], []).append(o)
    rounds = st.get('rounds', [])
    final_ok = bool(rounds) and rounds[-1]['rc'] == 0
    dirty0 = {x['decl'] for x in c0['dirty']}
    dirty1 = {x['decl'] for x in c1['dirty']}
    ax0 = {x['axiom']: x for x in c0['ax']}
    ax1 = {x['axiom']: x for x in c1['ax']}
    # rewritten declarations: parents of the facts of replaced occurrences
    rewritten_decls = set()
    replaced_facts = set()
    for o in occs:
        if o['status'] == 'replaced':
            for f in o.get('facts', []):
                rewritten_decls.add(f.split('._native.')[0])  # the declaration that used the tactic
                replaced_facts.add(f)
    still = sorted(dd for dd in rewritten_decls if dd in dirty1)
    why = {}
    for dd in still:
        own = [x for x in c1['ax'] if x['axiom'].split('._native.')[0] == dd]
        why[dd] = f'{len(own)} unconverted native facts of its own' if own else 'depends on another native-dependent declaration'
    # consistency: every native axiom after the rewrite comes from an occurrence that was kept (matched by its
    # declaration range in the rewritten coordinates; names are renumbered per declaration), and each kept
    # occurrence produces as many facts as before
    modfile_o = {o['module']: o['file'] for o in occs}
    by_newpos = {(o['file'], o['line'], o.get('new_col', o['col'])): o for o in occs}
    after_count, after_bad, after_unmatched = {}, [], []
    for x in c1['ax']:
        r = parse_rng(x['range'])
        o = by_newpos.get((modfile_o.get(x['module']), r[0], r[1])) if r else None
        if o is None:
            if x['tactic'] != 'bv_decide':
                after_unmatched.append(x['axiom'])
            continue
        if o['status'] == 'replaced':
            after_bad.append(x['axiom'])
        after_count[o['id']] = after_count.get(o['id'], 0) + 1
    count_mismatch = [o['id'] for o in occs if o['status'] != 'replaced' and o.get('facts')
                      and after_count.get(o['id'], 0) != len(o['facts'])]
    affected = plan['affected']
    replaced_mods = sorted({o['module'] for o in occs if o['status'] == 'replaced'})
    summary = dict(
        name=name, pkg=str(orig), toolchain=tc,
        uses=len(occs),
        replaced=sum(1 for o in occs if o['status'] == 'replaced'),
        replaced_known=sum(1 for o in occs if o['status'] == 'replaced' and o.get('facts')),
        replaced_unknown=sum(1 for o in occs if o['status'] == 'replaced' and not o.get('facts')),
        replaced_facts=len(replaced_facts),
        replaced_with_heartbeat_bump=sum(1 for o in occs if o['status'] == 'replaced' and o.get('bumped')),
        heartbeat_bumps=sum(len(v) for v in st.get('bumps', {}).values()),
        remaining={},
        native_axioms_before=len(c0['ax']), native_axioms_after=len(c1['ax']),
        bv_decide_axioms_before=sum(1 for x in c0['ax'] if x['tactic'] == 'bv_decide'),
        bv_decide_axioms_after=sum(1 for x in c1['ax'] if x['tactic'] == 'bv_decide'),
        axioms_after_as_expected=(not after_bad and not after_unmatched and not count_mismatch),
        axioms_after_from_replaced=after_bad[:20], axioms_after_unmatched=after_unmatched[:20],
        kept_occurrences_fact_count_mismatch=count_mismatch[:20],
        native_dependent_decls_before=len(dirty0), native_dependent_decls_after=len(dirty1),
        rewritten_decls=len(rewritten_decls), rewritten_decls_still_native=len(still), still_native_why=why,
        build_ok=final_ok, rounds=rounds,
        time0={k: st.get('time0', {}).get(k) for k in ('wall', 'cpu', 'n_built', 'peak_lean', 'rc', 'peak_rss_gb', 'peak_rss_sum_gb')},
        time1={k: st.get('time1', {}).get(k) for k in ('wall', 'cpu', 'n_built', 'peak_lean', 'rc', 'peak_rss_gb', 'peak_rss_sum_gb')},
        default_build=st.get('default_build'),
        census_failed=dict(before=c0['failed'], after=c1['failed']),
        census_complete=not c0['failed'] and not c1['failed'],
        affected_modules=len(affected), replaced_modules=len(replaced_mods),
        unmatched_axioms=sum(1 for x in plan.get('unmatched', []) if x['tactic'] != 'bv_decide'),
    )
    for o in occs:
        if o['status'] != 'replaced':
            summary['remaining'][o['reason']] = summary['remaining'].get(o['reason'], 0) + 1
    # per-module build times reported by Lake (affected modules, clean rebuilds before/after)
    b0, b1 = st.get('time0', {}).get('built', {}), st.get('time1', {}).get('built', {})
    mt = sorted(((m, b0.get(m), b1.get(m)) for m in affected if m in b0 and m in b1), key=lambda t: t[1] - t[2])
    summary['module_times_sum'] = [round(sum(t[1] for t in mt), 1), round(sum(t[2] for t in mt), 1)]
    summary['module_times_slower'] = [t for t in mt[:8] if t[2] > t[1]]
    summary['module_times_faster'] = [t for t in reversed(mt[-8:]) if t[2] < t[1]]
    (w / 'summary.json').write_text(json.dumps(summary, indent=1))
    patch = []
    for rel in sorted(occs_by_file):
        if any(o['status'] == 'replaced' for o in occs_by_file[rel]):
            p = subprocess.run(['diff', '-u', '--label', f'a/{rel}', '--label', f'b/{rel}', str(orig / rel), str(pkg / rel)],
                               capture_output=True, text=True)
            patch.append(p.stdout)
    (w / f'{name}.patch').write_text(''.join(patch))
    log(w, 'summary ' + json.dumps({k: summary[k] for k in ('uses', 'replaced', 'replaced_facts', 'native_axioms_before', 'native_axioms_after',
                                                          'axioms_after_as_expected', 'native_dependent_decls_before',
                                                          'native_dependent_decls_after', 'rewritten_decls_still_native', 'build_ok')}))

if __name__ == '__main__':
    main()
