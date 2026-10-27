#!/usr/bin/env python3
"""pinning_v4.py (v4: reads the rows the tables use: migrate s2_NAME > c2_NAME > s_NAME, switch
kf-c2-NAME > kf-NAME; each entry records its directory; v3: a `#guard_msgs` mismatch over an audit command or whose diff shows an audit
message is an axiom pin too; v2: minidregg's `#assert_compiled` pins ("compiled-pin REFUSED"); a `#guard_msgs`
mismatch counts as an axiom pin only when the guarded command is `#print axioms`, and as "message pin" when the
changed output is a kernel-first info message): classify the failed builds of the migrate and switch runs. Run as ntbuild.
A failed build is an "axiom-pinning check" when ALL its errors come from the project's own axiom-audit code and no
module fails without an error: messages of zcash's `assert_axioms ... +native(...)` ("reaches no native_decide
axiom", "depends on native_decide axiom(s)"), `#guard_msgs` expectations ("does not match generated message"),
`#assert_axioms`-style checks ("depends on axioms outside"), or an error located on an audit command
(`assert_axioms`, `#assert_axioms`, `#guard_msgs`, `#print axioms`) in the original source (lines L-3..L, for the
lines the switch inserts). Anything else is a "build failure".
Builds read: migrate's full build (mig/s_NAME/build_default.log, when its rc != 0) and every switch build with
rc != 0 (mig/kf-NAME/build_TAG.log). Writes runs/pinning.json and prints one line per failed build.
usage: pinning_v4.py"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import importlib.util, json, re
from pathlib import Path

W = Path((NT_BOX + '/runs'))
ROOT = W / 'mig'
spec = importlib.util.spec_from_file_location('nm', W / 'tools/ntrust_migrate_ms1.py')
nm = importlib.util.module_from_spec(spec)
spec.loader.exec_module(nm)
MSG = re.compile(r"reaches no native_decide axiom|depends on native_decide axiom|depends on axioms outside|"
                 r"compiled-pin REFUSED|rests on NO compiled-evaluation oracle")
GUARD = re.compile(r"does not match generated message")
CMD = re.compile(r'^\s*(?:assert_axioms|#assert_axioms|#assert_compiled)\b')
FAILED = re.compile(r'✖ \[\d+/\d+\] Building (\S+)')


def classify(log: Path, orig: Path):
    errs, failed = [], set()
    ll = log.read_text(errors='ignore').splitlines()
    for idx, l in enumerate(ll):
        m = nm.ERR_RE.match(l.strip())
        if m:
            msg = m.group(4)
            if GUARD.search(msg):  # look at the diff that follows for a kernel-first message
                diff = []
                for x in ll[idx + 1:idx + 40]:
                    if x.startswith(('error:', '✔', '✖', 'ℹ', 'info:', 'warning:')):
                        break
                    diff.append(x)
                if any('kernel-first' in x for x in diff if x[:1] in '+-'):
                    msg += ' [diff: kernel-first info message]'
                elif any(MSG.search(x) for x in diff if x[:1] in '+-'):
                    msg += ' [diff: audit message]'
            errs.append((m.group(1), int(m.group(2)), msg))
        m = FAILED.search(l)
        if m:
            failed.add(m.group(1))
    lines_of = {}
    mods = {}
    n_audit, n_msgpin, other_ex = 0, 0, []
    for f, ln, msg in errs:
        p = (orig / f)
        if f not in lines_of:
            try:
                lines_of[f] = p.read_text(errors='ignore').splitlines()
            except OSError:
                lines_of[f] = []
        mod = nm.module_of(p, nm.pkg_root_of(p, orig)) or f
        src = lines_of[f][max(0, ln - 4):ln]
        win = lines_of[f][max(0, ln - 4):ln + 3]
        if GUARD.search(msg):
            if 'kernel-first info message' in msg:
                audit = False
                n_msgpin += 1
            else:
                audit = ('audit message' in msg or
                         any('#print axioms' in x or CMD.match(x) or x.lstrip().startswith('assert_axioms') for x in win))
        else:
            audit = bool(MSG.search(msg)) or any(CMD.match(x) for x in src)
        n_audit += audit
        e = mods.setdefault(mod, [0, 0])
        e[0 if audit else 1] += 1
        if not audit and len(other_ex) < 5:
            other_ex.append(f'{f}:{ln}: {msg[:160]}')
    audit_mods = sorted(m for m, (a, o) in mods.items() if o == 0)
    other_mods = sorted(m for m, (a, o) in mods.items() if o)
    silent = sorted(x for x in failed if x not in mods)
    kind = 'axiom-pinning check' if errs and n_audit == len(errs) and not silent else 'build failure'
    return dict(kind=kind, n_errors=len(errs), n_audit=n_audit, n_message_pin_kernel_first=n_msgpin, audit_modules=audit_mods, other_modules=other_mods,
                failed_without_errors=silent, other_examples=other_ex)


def main():
    out = {}
    for l in open(W / 'pkgs24.tsv'):
        name, path = l.split('\t')[:2]
        orig = Path(path)
        md = next((ROOT / f'{p}{name}' for p in ('s2_', 'c2_', 's_') if (ROOT / f'{p}{name}' / 'summary.json').exists()),
                  ROOT / f's_{name}')
        sf = md / 'summary.json'
        if sf.exists():
            s = json.loads(sf.read_text())
            db = s.get('default_build') or {}
            if db.get('rc') not in (0, None) or not s.get('build_ok'):
                lg = md / 'build_default.log'
                if lg.exists():
                    out[f'mig {name} default'] = dict(classify(lg, orig), dir=str(md))
        kd = next((ROOT / f'{p}{name}' for p in ('kf-c2-', 'kf-') if (ROOT / f'{p}{name}' / 'kf_summary.json').exists()),
                  ROOT / f'kf-{name}')
        kf = kd / 'kf_summary.json'
        if kf.exists():
            for b in json.loads(kf.read_text()).get('builds', []):
                if b['rc'] != 0:
                    lg = kd / f"build_{b['tag']}.log"
                    if lg.exists():
                        out[f"kf {name} {b['tag']}"] = dict(classify(lg, orig), dir=str(kd))
    (W / 'pinning.json').write_text(json.dumps(out, indent=1))
    for k, v in out.items():
        print(k, v['kind'], f"errors={v['n_errors']} audit={v['n_audit']} audit_modules={len(v['audit_modules'])} "
                            f"other_modules={len(v['other_modules'])} silent={len(v['failed_without_errors'])}",
              v['other_examples'][:2])


if __name__ == '__main__':
    main()
