#!/usr/bin/env python3
"""Independent statement and axiom check of a kernel supplement written by `lake exe ntrust` (run as ntbuild), v2.

v2: when the types differ as expressions but are definitionally equal for the elaborator, the kernel is asked to
check it too: a theorem with the type of `T` and the value `T.kernel` is added to the environment (`addDecl`), which
succeeds only if the kernel finds the two types definitionally equal (counted as defeq_kernel).

usage: stmt_check.py OUT_DIR [--jobs N] [--mem GB]
For each supplement module K, a fresh Lean process imports K and, for every constant `T.kernel` declared in K,
compares its type with the type of `T` (Expr equality; when they differ, definitional equality at default
transparency) and lists the axioms `T.kernel` depends on beyond propext, Classical.choice and Quot.sound. As a
positive control it counts the originals `T` that depend on a non-standard axiom (all of them should). This does
not rely on the driver's own `same_statement` flag. Writes OUT_DIR/stmt/<i>.{lean,log} and OUT_DIR/stmt/summary.txt.
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import concurrent.futures as cf, json, os, re, subprocess, sys
from pathlib import Path

out = Path(sys.argv[1])
arg = lambda k, d: sys.argv[sys.argv.index(k) + 1] if k in sys.argv else d
jobs = int(arg('--jobs', '8')); mem = int(arg('--mem', '32'))
cj = json.loads((out / 'comparator.json').read_text())
mods = sorted({p['kernel_module'] for p in cj['pairs']})
proj = Path(cj['project'])
tc = (proj / 'lean-toolchain').read_text().strip().split(':')[-1]
lean = Path((NT_BOX + '/elan/toolchains')) / f"leanprover--lean4---{tc}" / 'bin' / 'lean'
env = dict(os.environ); env['LEAN_PATH'] = ':'.join(cj['lean_path']); env['LEAN_NUM_THREADS'] = '1'
W = out / 'stmt2'; W.mkdir(exist_ok=True)

SCRIPT = r'''
open Lean Elab Command in
#eval show CommandElabM Unit from do
  let env ← getEnv
  let some kidx := env.getModuleIdx? `{MOD}
    | IO.println "NOMODULE"
  let std := [``propext, ``Classical.choice, ``Quot.sound]
  let mut same := 0
  let mut defeq := 0
  let mut diff := 0
  let mut missing := 0
  let mut badAx := 0
  let mut origNative := 0
  let mut kdefeq := 0
  for (k, ki) in env.constants.map₁.toList do
    if env.getModuleIdxFor? k != some kidx then continue
    if !(k matches .str _ "kernel") then continue
    let t := k.getPrefix
    if (← collectAxioms t).any (fun a => !std.contains a) then
      origNative := origNative + 1
    match env.find? t with
    | none =>
      missing := missing + 1
      IO.println s!"MISSING {t}"
    | some ti =>
      if ti.type == ki.type then
        same := same + 1
      else if (← liftTermElabM (Meta.isDefEq ti.type ki.type)) then
        defeq := defeq + 1
        IO.println s!"DEFEQ {t}"
        let lvls := ti.levelParams.map Level.param
        let chkName := k ++ `ntStmtCheck
        let tv : TheoremVal := { name := chkName, levelParams := ti.levelParams, type := ti.type, value := mkConst k lvls, all := [chkName] }
        try
          liftCoreM (addDecl (.thmDecl tv))
          kdefeq := kdefeq + 1
          IO.println s!"KERNEL_DEFEQ_OK {t}"
        catch e =>
          IO.println s!"KERNEL_DEFEQ_FAIL {t}: {← e.toMessageData.toString}"
      else
        diff := diff + 1
        IO.println s!"DIFF {t}"
    let axs ← collectAxioms k
    let bad := axs.filter (fun a => !std.contains a)
    if !bad.isEmpty then
      badAx := badAx + 1
      IO.println s!"AXIOMS {k} {bad.toList}"
  IO.println s!"STMT same={same} defeq={defeq} diff={diff} missing={missing} nonstd_axioms={badAx} control_originals_nonstd={origNative} defeq_kernel={kdefeq}"
'''


def one(item):
    i, mod = item
    src = W / f"{i}.lean"
    src.write_text(f"import {mod}\n" + SCRIPT.replace('{MOD}', mod))
    with open(W / f"{i}.log", 'w') as f:
        rc = subprocess.run(['bash', '-c', f'ulimit -v {mem * 1024 * 1024}; ulimit -s unlimited; exec timeout -k 30 1800 "$@"', 'x',
                             str(lean), '-j1', '--tstack=1048576', str(src)], cwd=W, env=env, stdout=f, stderr=subprocess.STDOUT).returncode
    t = (W / f"{i}.log").read_text(errors='ignore')
    m = re.search(r'STMT same=(\d+) defeq=(\d+) diff=(\d+) missing=(\d+) nonstd_axioms=(\d+) control_originals_nonstd=(\d+) defeq_kernel=(\d+)', t)
    return mod, rc, tuple(int(x) for x in m.groups()) if m else None


tot = [0] * 7; bad = []
with cf.ThreadPoolExecutor(jobs) as ex:
    for mod, rc, r in ex.map(one, enumerate(mods)):
        if r is None:
            bad.append(f"{mod} rc={rc}")
            continue
        tot = [a + b for a, b in zip(tot, r)]
lines = [f"modules={len(mods)} pairs_in_json={len(cj['pairs'])} kernel_theorems_checked={sum(tot[:3])} same={tot[0]} "
         f"defeq_only={tot[1]} different={tot[2]} missing_original={tot[3]} nonstandard_axioms={tot[4]} control_originals_with_nonstandard_axioms={tot[5]} defeq_checked_by_kernel={tot[6]} modules_failed={len(bad)}"] + bad
(W / 'summary.txt').write_text('\n'.join(lines) + '\n')
print('\n'.join(lines))
