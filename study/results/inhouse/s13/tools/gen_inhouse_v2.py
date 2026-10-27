#!/usr/bin/env python3
"""gen_inhouse_v2.py (S(13) probe; v2: kernel_ms only from the PROVED line, driver-run axioms from
the #native_axioms listing in probe_l1): writes the per-run table, the per-fact table and the triage table of
the S(13) >= 45 NativeTrust probe into OUT (the in-house layout). Run as ntbuild on the box.
usage: gen_inhouse_v1.py S13DIR OUT AXIOMS_TXT
  S13DIR: $NT_BOX/work_iterstr/s13 (probe_* dirs with the per-run logs and MANIFEST.tsv files)
  OUT: the in-house directory (logs/ must already hold copies of the per-run logs, as logs/<probe dir>/<id>.log)
  AXIOMS_TXT: the release's logs/s45_unconditional_axioms.txt (#print axioms of Sortnet.S13_ge_45)
"""
import os as _nt_os
NT_BOX = _nt_os.environ.get('NT_BOX', '/home/ntbuild')  # box root used in the study; set NT_BOX to run elsewhere
import os, re, sys

S13, OUT, AXF = sys.argv[1:4]

# runs: (probe dir, mode, timeout s, memory cap GB, thread stack KB, orchestrator)
RUNDIRS = [("probe_v1", "restated", 900, 48, 1048576), ("probe_d1", "driver", 900, 48, 1048576),
           ("probe_v1h", "restated", 3600, 96, 1048576), ("probe_v1h2", "restated", 3600, 96, 1048576),
           ("probe_v1s", "restated", 3600, 96, 33554432)]
DRIVER_FACTS = {  # probe_d1 files: module, axiom (index -> axiom from `#native_axioms`, probe_l1/L_list.log)
    "D_header_0": ("S45Final.Main.Header", "Sortnet.S45Final.Main.header_info._native.native_decide.ax_1_1"),
    "D_header_1": ("S45Final.Main.Header", "Sortnet.S45Final.Main.final_ok._native.native_decide.ax_1_1"),
    "D_bfsD00_0": ("S45Final.Main.Bfs.D00C000", "Sortnet.S45Final.Main.Bfs.D00C000.bfs._native.native_decide.ax_1_1"),
    "D_bfsD24_0": ("S45Final.Main.Bfs.D24C000", "Sortnet.S45Final.Main.Bfs.D24C000.bfs._native.native_decide.ax_1_1"),
    "D_ct4_0": ("S45DataCt4.Slice", "Sortnet.S45.BFS.ct4_bfs_d12._native.native_decide.ax_1_1"),
    "D_small_0": ("S13.S11.Small", "Sortnet.certOK_5._native.native_decide.ax_1_1")}

def modname(path):
    return path[:-5].replace("/", ".") if path.endswith(".lean") else path

def klass(fid, ax):
    a = ax or ""
    if ".Stage2.Run.c" in a: return "stage2_root_chunk"
    if ".Main.Kl." in a: return "kl_chunk"
    if ".Main.Bfs." in a: return "bfs_chunk"
    if "T9Hint7Check" in a: return "hint_chunk"
    if a.endswith("header_info._native.native_decide.ax_1_1") or a.endswith("final_ok._native.native_decide.ax_1_1"):
        return "header"
    if ".Stage2.Run.entries" in a: return "entries"
    if "certOK_harder11" in a: return "s11_certificate"
    return "test_fact_not_in_S13_ge_45"

def classify(txt, rc):
    """The driver's classification (NativeTrust/Driver/Main.lean, classify), with the cases it cannot see here."""
    if rc is None:
        return "ERROR", "memory (OOM kill at the cap; systemd stopped the scope, no rc line)"
    verdict = "TIMEOUT" if rc == 124 else "ERROR"
    if "PROVED `" in txt: verdict = "PROVED"
    elif "FAILED `" in txt: verdict = "FAILED"
    reason = ""
    if verdict == "ERROR":
        if "Stack overflow" in txt: reason = "stack"
        elif rc in (134, 137) and "deep recursion" in txt: reason = "memory (after kernel deep-recursion rejections of the data-chunk copies)"
        elif rc in (134, 137): reason = "memory"
        else: reason = f"rc{rc}"
    elif verdict == "TIMEOUT":
        reason = "timeout"
    return verdict, reason

def num_after(txt, key):
    m = re.search(re.escape(key) + r"(\d+)", txt)
    return m.group(1) if m else ""

def kms(txt):
    m = re.search(r"PROVED `[^`]+` as `[^`]+`: kernel_ms=(\d+)", txt)
    return m.group(1) if m else ""

rows = []
for d, mode, tmo, mem, tstack in RUNDIRS:
    man = {}
    mp = os.path.join(S13, d, "MANIFEST.tsv")
    if os.path.exists(mp):
        for line in open(mp):
            f = line.rstrip("\n").split("\t")
            man[f[0]] = (modname(f[1]), f[3])
    for fn in sorted(os.listdir(os.path.join(S13, d))):
        if not fn.endswith(".log"):
            continue
        fid = fn[:-4]
        txt = open(os.path.join(S13, d, fn), errors="replace").read()
        m = re.search(r"^rc=(\d+)", txt, re.M)
        rc = int(m.group(1)) if m else None
        verdict, reason = classify(txt, rc)
        if fid in man:
            mod, ax = man[fid]
        elif d == "probe_v1h" or d == "probe_v1h2" or d == "probe_v1s":
            mod, ax = "", ""
            for line in open(os.path.join(S13, "probe_v1", "MANIFEST.tsv")):
                f = line.rstrip("\n").split("\t")
                if f[0] == fid: mod, ax = modname(f[1]), f[3]
        else:
            mod, ax = DRIVER_FACTS[fid]
        secs = num_after(txt, " secs ").split(".")[0] if " secs " in txt else ""
        m3 = re.search(r"maxrss_kb (\d+) secs ([\d.]+)", txt)
        if m3: secs = str(round(float(m3.group(2))))
        rows.append([mod, ax, "native_decide", "false", verdict, reason, secs, "", kms(txt),
                     m3.group(1) if m3 else "", "", f"logs/{d}/{fn}", mode, d, fid, str(tmo), str(mem), str(tstack),
                     klass(fid, ax)])

hdr = ["module", "axiom", "tactic", "inner", "verdict", "reason", "seconds", "blockers", "kernel_ms", "maxrss_kb",
       "fact_module", "log", "mode", "run_dir", "run_id", "timeout_s", "memory_cap_gb", "tstack_kb", "class"]
with open(os.path.join(OUT, "s13_probe.ax.tsv"), "x") as f:
    f.write("\t".join(hdr) + "\n")
    for r in rows:
        f.write("\t".join(r) + "\n")

# static triage (one representative fact per class; probe_t1)
tri = []
for fn in sorted(os.listdir(os.path.join(S13, "probe_t1"))):
    if not fn.endswith(".log"):
        continue
    for line in open(os.path.join(S13, "probe_t1", fn), errors="replace"):
        if line.startswith("TRIAGE "):
            fid = line.split()[1].rstrip(":")
            tri.append([fid, "-", line.split(":", 1)[1].strip(), "-"])
        elif line.startswith("BLOCKER "):
            parts = line.rstrip("\n").split(" | ")
            head = parts[0].split()
            tri.append([head[1], head[2], parts[1] if len(parts) > 1 else "", parts[2][5:] if len(parts) > 2 else ""])
with open(os.path.join(OUT, "s13_triage.tsv"), "x") as f:
    f.write("run_id\tblocker\treason\tpath\n")
    for r in tri:
        f.write("\t".join(r) + "\n")

# all native facts of Sortnet.S13_ge_45
txt = open(AXF).read()
axs = [a.strip() for a in re.search(r"\[(.*)\]", txt, re.S).group(1).split(",")]
axs = [a for a in axs if "._native." in a]
BLK = {"stage2_root_chunk": "ByteArray.hash; mixHash; System.Platform.getNumBits; Lean.Loop.forIn",
       "kl_chunk": "ByteArray.hash; mixHash; System.Platform.getNumBits",
       "hint_chunk": "ByteArray.hash; mixHash; System.Platform.getNumBits",
       "bfs_chunk": "none", "header": "none", "entries": "none", "s11_certificate": "none"}
REP = {"stage2_root_chunk": "T_R_C00000", "kl_chunk": "T_KL_C000", "hint_chunk": "T_H_chunk00",
       "bfs_chunk": "T_BFS_D00C000", "entries": "T_S_entries", "s11_certificate": "T_S_certOK_harder11"}
def module_of(a):
    b = a.split("._native.")[0]
    if ".Stage2.Run.c" in b:
        return "S45Stage2Run.C" + b.split(".Stage2.Run.c")[1]
    if ".Main.Kl." in b or ".Main.Bfs." in b:
        return "S45Final.Main." + ".".join(b.split(".")[3:5])
    if "T9Hint7Check.chunk" in b:
        return "S45Data.T9Hint7Check.Chunk" + b.split(".chunk")[1]
    if b.endswith("header_info") or b.endswith("final_ok"):
        return "S45Final.Main.Header"
    if b.endswith(".Stage2.Run.entries"):
        return "S45Stage2Run.Entries"
    if b.endswith("certOK_harder11"):
        return "S13.S11.Main"
    return ""
runs_by_ax = {}
for r in rows:
    runs_by_ax.setdefault(r[1], []).append(f"{r[13]}/{r[14]}:{r[4]}")
with open(os.path.join(OUT, "s13_facts.tsv"), "x") as f:
    f.write("axiom\tmodule\tclass\tstatic_blockers_of_class\ttriage_representative\truns\n")
    for a in axs:
        k = klass("", a)
        blk = BLK.get(k, "")
        rep = REP.get(k, "T_S_header_info / T_S_final_ok" if k == "header" else "")
        if a.startswith("Sortnet.Stage2.Run.c00793s2."):
            blk, rep = "not triaged: the one root chunk with a skipped leaf attempt (rootsOKS)", ""
        f.write("\t".join([a, module_of(a), k, blk, rep, ",".join(runs_by_ax.get(a, []))]) + "\n")
print(f"{len(rows)} runs, {len(tri)} triage lines, {len(axs)} native facts")
