#!/usr/bin/env python3
"""gen_probes_v1.py (S(13) probe): writes one Lean file per sampled native fact of the published
S(13) >= 45 project. Each file re-states the fact's `native_decide` statement in the module's own imports, namespace
and `open`s, and runs the driver's per-fact step on it: `proveTrueSplit (decide stmt) name [] cfg (native? := some
true)` with cfg = { split := 8, trace := true, native := false }, as `prove_native_axiom_nth M i (config := { split :=
8, trace := true })` does, under the driver's options. Output: PROVED/FAILED lines in the driver's format.
usage: gen_probes_v1.py TREE SAMPLE.tsv OUTDIR   (SAMPLE: id, module file, theorem name as written, extra imports or -)
"""
import os, re, sys

HEADER_OPTS = ("set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n"
               "set_option nativeTrust.eprint true\n")

def probe(tree, fid, modfile, thm, extra):
    src = open(os.path.join(tree, modfile)).read()
    lines = src.split("\n")
    imports = [l for l in lines if l.startswith("import ")]
    if extra != "-":
        imports = ["import " + m for m in extra.split(",")]
    pat = re.compile(r"theorem\s+" + re.escape(thm) + r"\s*:\s*(?P<stmt>.*?)\s*:=\s*by\s+native_decide", re.S)
    m = pat.search(src)
    if not m:
        raise SystemExit(f"{fid}: theorem {thm} not found in {modfile}")
    stmt = " ".join(m.group("stmt").split())
    # namespace and open context at the theorem
    before = src[:m.start()].split("\n")
    ctx, ns = [], []
    for l in before:
        s = l.strip()
        if s.startswith("namespace "):
            ns.append(s.split()[1]); ctx.append(s)
        elif s.startswith("end ") and ns and s.split()[1] == ns[-1]:
            ns.pop(); ctx.append(s)
        elif s.startswith("open ") and not s.endswith(" in"):
            ctx.append(s)
    full = ".".join(ns + [thm]) if not thm.startswith("Sortnet.") else thm
    ax = f"{full}._native.native_decide.ax_1_1"
    body = f'''import NativeTrust
{chr(10).join(imports)}
{HEADER_OPTS}
/-! Probe {fid}: the driver's per-fact step on the statement of `{full}`
({modfile}), without building the chunk theorem natively. -/

{chr(10).join(ctx)}

open Lean Meta Elab Term NativeTrust in
#eval show TermElabM Unit from do
  let t0 ← IO.monoMsNow
  IO.println s!"START {fid}"
  let p ← elabTerm (← `({stmt})) (some (mkSort .zero))
  synthesizeSyntheticMVarsNoPostponing
  let e ← mkDecide (← instantiateMVars p)
  let ax := `{ax}
  let name := (`_s13probe).str "{fid}"
  let cfg : KernelConfig := {{ split := 8, trace := true, native := false }}
  IO.println s!"STATEMENT_MS {{(← IO.monoMsNow) - t0}}"
  try
    let r ← proveTrueSplit e name [] cfg (native? := some true)
    IO.println s!"PROVED `{{ax}}` as `{{r.thm}}`: kernel_ms={{r.ms}} copies={{r.copies.size}} \\
      total_ms={{(← IO.monoMsNow) - t0}} pieces={{r.pieces}} axioms={{(← collectAxioms r.thm).toList}}"
  catch ex =>
    let msg := (← ex.toMessageData.toString).replace "\\n" " | "
    IO.println s!"FAILED `{{ax}}`: total_ms={{(← IO.monoMsNow) - t0}} {{msg}}"
'''
    for n in reversed(ns):
        body += f"\nend {n}\n"
    return body, full, ax, stmt

def main():
    tree, sample, out = sys.argv[1:4]
    os.makedirs(out, exist_ok=False)
    man = open(os.path.join(out, "MANIFEST.tsv"), "w")
    for line in open(sample):
        if not line.strip() or line.startswith("#"):
            continue
        fid, modfile, thm, extra = line.rstrip("\n").split("\t")
        body, full, ax, stmt = probe(tree, fid, modfile, thm, extra)
        open(os.path.join(out, fid + ".lean"), "x").write(body)
        man.write(f"{fid}\t{modfile}\t{full}\t{ax}\t{stmt}\n")
    man.close()

main()
