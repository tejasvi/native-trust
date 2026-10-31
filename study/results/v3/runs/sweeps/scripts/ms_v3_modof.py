#!/usr/bin/env python3
"""ms_v3_modof.py PKG [PKG...]: the defining module of every definition that the v3 default run copied (well-founded
replacement) in each package, from Lean's environment (run on the box as ntbuild with python3 -I, in a capped scope).
For PKG: the copied names (agg/v2/copies_<PKG>.tsv, written by ms_v3_copies.py), the modules of the facts whose logs
made copies (results v3-<PKG> with v3r-<PKG> laid over), one `lean -j1` process importing those modules and printing
env.getModuleIdxFor? of each name; LEAN_PATH as the v3 driver computes it (lake env printenv LEAN_PATH in the package
directory). Classes: core (Init, Std, Lean), library (Mathlib, Batteries, Aesop, Qq, Plausible, ProofWidgets,
ImportGraph, LeanSearchClient), project (any other module). Writes agg/v2/modof_<PKG>.tsv (name, module, class) and
prints counts."""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import collections, os, re, subprocess, sys
from pathlib import Path

H = Path(NT_BOX)
A = H / 'v3' / 'sweeps' / 'agg' / 'v2'
DIRS = {'strata': 'repos/Strata', 'cvc5-logos': 'repos/cvc5-logos', 'cedar-lean': 'repos/cedar-spec/cedar-lean',
        'formal-conjectures': 'repos/formal-conjectures', 'berry-esseen': 'repos/berry-esseen',
        'humanfia-icho2026': 'repos/humanfia-hoa/icho2026/gpt-5.6-sol-full68-formalization',
        'asi-stack-book': 'repos/asi-stack-book/lean'}
CORE = ('Init', 'Std', 'Lean')
LIBS = ('Mathlib', 'Batteries', 'Aesop', 'Qq', 'Plausible', 'ProofWidgets', 'ImportGraph', 'LeanSearchClient')
PROVED_RE = re.compile(r'^PROVED `([^`]+)`', re.M)
COPIES_RE = re.compile(r'^NT \S+ blockers_ms=\d+ bounded=\w+ copy_ms=\d+ copies=(\d+)', re.M)
IDENT_RE = re.compile(r"^[A-Za-z_][A-Za-z0-9_'!?]*$")


def esc(m):
    return '.'.join(c if IDENT_RE.match(c) else f'«{c}»' for c in m.split('.'))


def main():
    for p in sys.argv[1:]:
        names = [l.split('\t')[0] for l in (A / f'copies_{p}.tsv').read_text().splitlines() if l]
        rows = {}
        for run in (f'v3-{p}', f'v3r-{p}'):
            f = H / 'results' / f'{run}.ax.tsv'
            if f.exists():
                for l in f.read_text(errors='ignore').splitlines():
                    c = l.split('\t')
                    if len(c) >= 7:
                        rows[c[2]] = c[1]
        mods = set()
        for run in (f'v3-{p}', f'v3r-{p}'):
            w = H / 'work' / run
            if w.is_dir():
                for lg in w.glob('ax[12]*_*.log'):
                    t = lg.read_text(errors='ignore')
                    m = PROVED_RE.search(t)
                    if m and sum(int(x) for x in COPIES_RE.findall(t)) > 0 and m.group(1) in rows:
                        mods.add(rows[m.group(1)])
        tc = (H / DIRS[p] / 'lean-toolchain').read_text().strip().split(':')[-1]
        L = H / 'elan' / 'toolchains' / f'leanprover--lean4---{tc}'
        e = dict(os.environ, ELAN_HOME=str(H / 'elan'), PATH=f'{H}/elan/bin:' + os.environ.get('PATH', '/usr/bin:/bin'))
        lp = subprocess.run(['lake', 'env', 'printenv', 'LEAN_PATH'], cwd=H / DIRS[p], env=e, capture_output=True,
                            text=True, timeout=600, stdin=subprocess.DEVNULL).stdout.strip()
        e['LEAN_PATH'] = lp
        e['LEAN_NUM_THREADS'] = '1'
        src = A / f'modof_{p}.lean'
        lits = ', '.join('"' + n.replace('\\', '\\\\').replace('"', '\\"') + '"' for n in names)
        src.write_text(''.join(f'import {esc(m)}\n' for m in sorted(mods)) +
                       'open Lean in\ndef parseN (s : String) : Name := (s.splitOn ".").foldl (fun n c => match c.toNat? with '
                       '| some k => Name.mkNum n k | none => Name.mkStr n ((c.replace "«" "").replace "»" "")) Name.anonymous\n'
                       'open Lean in\n#eval show CoreM Unit from do\n  let env ← getEnv\n'
                       f'  for s in [{lits}] do\n'
                       '    match env.getModuleIdxFor? (parseN s) with\n'
                       '    | some i => IO.println s!"MODOF\\t{s}\\t{env.header.moduleNames[i.toNat]!}"\n'
                       '    | none => IO.println s!"MODOF\\t{s}\\t-"\n')
        r = subprocess.run(['bash', '-c', 'ulimit -v 50331648; exec timeout -k 30 900 "$@"', 'cap', str(L / 'bin' / 'lean'), '-j1',
                            str(src)], cwd=A, env=e, capture_output=True, text=True, stdin=subprocess.DEVNULL)
        got = dict(tuple(l.split('\t')[1:3]) for l in r.stdout.splitlines() if l.startswith('MODOF\t'))
        cls = collections.Counter()
        out = []
        for n in names:
            m = got.get(n, '?')
            root = m.split('.')[0]
            c = 'core' if root in CORE else 'library' if root in LIBS else 'unknown' if m in ('?', '-') else 'project'
            cls[c] += 1
            out.append(f'{n}\t{m}\t{c}')
        (A / f'modof_{p}.tsv').write_text('\n'.join(out) + '\n')
        print(f'{p}\trc={r.returncode}\tmodules_imported={len(mods)}\tnames={len(names)}\t' + ' '.join(f'{k}={v}' for k, v in sorted(cls.items()))
              + ('' if r.returncode == 0 else '\t' + r.stdout[-300:].replace('\n', ' ') + r.stderr[-300:].replace('\n', ' ')))


if __name__ == '__main__':
    main()
