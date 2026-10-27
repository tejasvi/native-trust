import NativeTrust.Driver.Project
import NativeTrust.Driver.Migrate

/-!
# `ntrust`: one command from native facts to kernel-checked proofs

`lake exe ntrust` in the root of a Lake project that has NativeTrust on its `LEAN_PATH` (a
`require` of the `native_trust` package), or with `--nt-lib DIR` pointing to NativeTrust's
`.lake/build/lib/lean`. A port of the Python driver `ops/m2_axioms4.py` (52,821-fact study) plus a
kernel supplement. The project itself is not changed; everything goes to the output directory
`OUT` (default `.ntrust`).

1. Finds the project's `.lean` files (outside `.lake`) that mention native evaluation, derives
   their module names, and `lake build`s those without an up-to-date `.olean`.
2. Takes the project's search path from `lake env printenv LEAN_PATH`, NativeTrust's library
   directory first, `OUT/mods` last.
3. Per module `M`, a generated file runs `#native_axioms M` (the facts: one per
   `native_decide`/`bv_decide`/`decide +native` use) and `#native_theorems M`, and prints `M`'s
   import closure and the native axioms each listed theorem depends on.
4. Phase 1: each fact used inside a definition (`inner`) is proved by
   `prove_native_axiom_nth M i` in its own `lean` process, compiled with `-o` to a module
   `OUT/mods/F1_…` that registers the kernel proof. Phase 2: every other fact the same way
   (`F2_…`), importing the phase-1 modules whose facts lie in the import closure of its module,
   so nested facts are reused, not re-proved. Each process runs under `timeout -k 30`, an
   address-space cap (`ulimit -v`) and `nativeTrust.eprint`, at most `--jobs` at a time.
5. `OUT/report.tsv`: one line per fact.
6. Kernel supplement: for each module `M` with theorems none of whose facts failed,
   `OUT/Kernel/<M>.lean` imports `NativeTrust`, `M` and the fact modules it needs and runs
   `trust_check_nth M i` for those theorems (indices from `#native_theorems M`; theorems with a
   fact this run did not check, e.g. outside `--modules`, go last, since `trust_check` proves
   such facts itself); compiling it (`lean -o`, cwd `OUT`, module `Kernel.<M>`) adds `T.kernel`
   for each theorem `T`, reusing the registered proofs. `lean -o` writes nothing when the
   process dies or a command fails; the module is then compiled once more with only the
   theorems that were kernelized. Verdicts in `OUT/theorems.tsv`; kernelized pairs in
   `OUT/comparator.json`.

Limitations: theorems in modules whose source does not mention native evaluation (they use
facts only through imports) get no supplement; the time limit of a supplement module
(`--kernel-timeout`) covers all its theorems; Linux tools (`bash`, coreutils `timeout`,
optionally `/usr/bin/time` for `maxrss_kb`).

## Output files

`report.tsv` (header line first), one line per fact: `module`, `axiom`, `tactic`, `inner`,
`verdict` (`PROVED`, `FAILED`, `TIMEOUT`, `ERROR`; `NOT_BUILT`/`LIST_ERROR` with axiom `-` for a
module that could not be built or listed), `reason`, `seconds`, `blockers` (constants without a
kernel definition reported by the check), then `kernel_ms`, `maxrss_kb`, `fact_module`, `log`.

`theorems.tsv` (header line first), one line per theorem that depends on a native fact:
`module`, `theorem`, `verdict` (`KERNELIZED`, `REJECTED`, or `TIMEOUT`/`ERROR` when the supplement
process ended without a verdict for it), `kernel_theorem`, `reason` (`trust_check`: the verdict of
`trust_check_nth`; `fact_not_converted`: a native fact it depends on was not converted, so it was
not checked), `direct_facts`, `all_facts`, `detail`.

`comparator.json`:
```
{ "format": "ntrust-comparator/1",
  "project": <project root>,
  "lean_path": [<directories under which the kernel modules load: NativeTrust, the project's
                LEAN_PATH, OUT/mods, OUT>],
  "permitted_axioms": ["propext", "Classical.choice", "Quot.sound"],
  "pairs": [ { "module": <source module of the theorem (names in Lean syntax)>,
               "theorem": <original theorem, proved with native evaluation>,
               "kernel_module": <supplement module "Kernel.<module>" (OUT/Kernel/<module>.olean)>,
               "kernel_theorem": <its kernel-checked counterpart, T.kernel>,
               "same_statement": <true: the type of kernel_theorem is the type of theorem,
                                  expression for expression>,
               "statement_rebuilt": [<when not: definitions carrying native proofs that the
                                     statement mentions, replaced by rebuilt copies,
                                     definitionally equal by proof irrelevance>] } ] }
```
Every `kernel_theorem` listed depends only on the `permitted_axioms` (checked by `trust_check`).

Exit code: 0 when every fact was converted and every theorem kernelized, 1 when some were not,
2 on a usage or setup error.
-/

namespace NativeTrust.Driver

open System

structure Opts where
  jobs : Nat := 4
  factTimeout : Nat := 900
  factMem : Nat := 48
  split : Nat := 8
  kernelTimeout : Nat := 3600
  out : String := ".ntrust"
  skipBuild : Bool := false
  ntLib : Option String := none
  modules : Option (Array String) := none
  help : Bool := false

def usage : String :=
"usage: lake exe ntrust [options]     (in the root directory of a Lake project)

Converts the project's native_decide / bv_decide / decide +native facts into proofs that Lean's
kernel checks, and writes a kernel supplement: a module per source module with `T.kernel` for
every theorem T whose native facts were all converted. The project is not changed.

options:
  --jobs N            processes at the same time (default 4)
  --fact-timeout S    time limit per fact, seconds (default 900)
  --fact-mem GB       address-space cap per process, GB (default 48)
  --split K           split a kernel check along && and List.all into up to K declarations
                      (default 8)
  --kernel-timeout S  time limit per supplement module, seconds (default 3600)
  --out DIR           output directory (default .ntrust)
  --skip-build        do not run `lake build` for modules without an up-to-date .olean
  --nt-lib DIR        NativeTrust's .lake/build/lib/lean (default: found on the project's
                      LEAN_PATH, e.g. through `require native_trust`)
  --modules M1,M2     only these modules
  -h, --help          this text

outputs in DIR: report.tsv (a line per fact), theorems.tsv (a line per theorem that depends on a
native fact), comparator.json (theorem / kernel theorem pairs), Kernel/<module>.lean (the
supplement), mods/ (a module per fact, registering its kernel proof), logs/, driver.log.
Exit code 0: everything converted; 1: some facts or theorems not; 2: usage or setup error.

lake exe ntrust migrate [options]: rewrite the project's native_decide / decide +native uses that
the kernel checks into decide +kernel, in place, verified by a build (`lake exe ntrust migrate
--help`)."

partial def parseArgs : List String → Opts → Except String Opts
  | [], o => .ok o
  | a :: rest, o =>
    -- `--opt=value` is `--opt value`
    match a.splitOn "=" with
    | k :: v :: vs =>
      if k.startsWith "--" then parseArgs (k :: "=".intercalate (v :: vs) :: rest) o
      else .error s!"unexpected argument `{a}`"
    | _ =>
      let nat (k : String) (f : Nat → Opts) : Except String Opts :=
        match rest with
        | v :: rest' =>
          match v.toNat? with
          | some n => parseArgs rest' (f n)
          | none => .error s!"{k} expects a number, got `{v}`"
        | [] => .error s!"{k} expects a value"
      let str (k : String) (f : String → Opts) : Except String Opts :=
        match rest with
        | v :: rest' => parseArgs rest' (f v)
        | [] => .error s!"{k} expects a value"
      match a with
      | "--jobs" => nat a fun n => { o with jobs := max 1 n }
      | "--fact-timeout" => nat a fun n => { o with factTimeout := max 1 n }
      | "--fact-mem" => nat a fun n => { o with factMem := max 1 n }
      | "--split" => nat a fun n => { o with split := max 1 n }
      | "--kernel-timeout" => nat a fun n => { o with kernelTimeout := max 1 n }
      | "--out" => str a fun v => { o with out := v }
      | "--nt-lib" => str a fun v => { o with ntLib := some v }
      | "--modules" => str a fun v =>
          { o with modules := some ((v.splitOn ",").filter (· != "")).toArray }
      | "--skip-build" => parseArgs rest { o with skipBuild := true }
      | "-h" | "--help" => parseArgs rest { o with help := true }
      | _ => .error s!"unknown option `{a}`"

/-- One native fact: the `index`-th axiom listed by `#native_axioms mod`. -/
structure Fact where
  mod : ModName
  axiomName : String
  tactic : String
  inner : Bool
  idx : Nat

structure FactResult where
  fact : Fact
  verdict : String
  reason : String := ""
  secs : Nat := 0
  blockers : String := ""
  kernelMs : String := ""
  maxrss : String := ""
  /-- The module in `OUT/mods` that registers the kernel proof (when `PROVED`). -/
  factModule : Option String := none
  log : String := ""

/-- One theorem listed by `#native_theorems mod`. -/
structure Thm where
  mod : ModName
  name : String
  direct : Nat
  all : Nat
  idx : Nat

structure ModInfo where
  mod : ModName
  facts : Array Fact := #[]
  thms : Array Thm := #[]
  /-- The modules `mod` imports, directly or not (raw dotted names). -/
  closure : Std.HashSet String := {}
  /-- Theorem index ↦ the native axioms it depends on; `none` if the listing did not get there. -/
  deps : Option (Std.HashMap Nat (Array String)) := none
  rc : UInt32 := 0
  log : String := ""

structure ThmRow where
  thm : Thm
  verdict : String
  kernelThm : String := ""
  reason : String := ""
  detail : String := ""
  statementRebuilt : String := ""

/-- First occurrences only (the first directory that has a module wins anyway). -/
def dedup (xs : Array String) : Array String := Id.run do
  let mut seen : Std.HashSet String := {}
  let mut out := #[]
  for x in xs do
    unless seen.contains x do
      seen := seen.insert x
      out := out.push x
  return out

def removeIfExists (p : FilePath) : IO Unit := do
  if ← p.pathExists then IO.FS.removeFile p

/-- Python driver's `classify`: verdict and reason of a fact check from its exit code and log. -/
def classify (rc : UInt32) (b : ByteArray) (factTimeout : Nat) : String × String := Id.run do
  let mut verdict := if rc == 124 then "TIMEOUT" else "ERROR"
  if bytesContainsWord b "PROVED `" then verdict := "PROVED"
  else if bytesContainsWord b "FAILED `" then verdict := "FAILED"
  let mut reason := ""
  if verdict == "PROVED" then
    if let some n := bytesNatAfter? b "acc_fallback=" then
      if n > 0 then reason := "acc_fallback"
  if verdict == "FAILED" then
    reason :=
      if bytesContains b "evaluates the decision procedure to `false`" then "false_in_logic"
      else if bytesContains b "non-standard axioms" then "other_axiom"
      else if bytesContains b "deterministic timeout" && bytesContains b "evaluation was bounded"
        then "blocked"
      else if bytesContains b "cannot unfold" then "blocked"
      else if bytesContains b "deterministic timeout" then "heartbeats"
      else if bytesContains b "internal error" then "bridge"
      else "other"
  else if verdict == "ERROR" then
    reason :=
      if bytesContains b "maximum recursion depth" then "maxRecDepth"
      else if bytesContains b "deep recursion" then "deep_recursion"
      else if bytesContains b "Stack overflow" || bytesContains b "stack overflow" then "stack"
      else if bytesContains b "out of memory" || bytesContains b "std::bad_alloc" || rc == 134 ||
        rc == 137 then "memory"
      else s!"rc{rc}"
  else if verdict == "TIMEOUT" then
    reason := s!"{factTimeout}s"
  return (verdict, reason)

/-- The generated file that lists the facts and theorems of `m`. -/
def listingSource (m : ModName) : String :=
  s!"import NativeTrust\nimport {m.esc}\n#native_axioms {m.esc}\n#native_theorems {m.esc}\n" ++
  "open Lean in\n#eval show CoreM Unit from do\n" ++
  "  IO.println \"NTMODS\"\n" ++
  "  for n in (← getEnv).header.moduleNames do\n" ++
  "    IO.println s!\"MOD\\t{n.toString (escape := false)}\"\n" ++
  "open Lean in\n#eval show CoreM Unit from do\n" ++
  "  IO.println \"NTDEPS\"\n" ++
  s!"  let thms ← NativeTrust.nativeTheoremsOf {m.nameTerm}\n" ++
  "  let mut i := 0\n" ++
  "  for (n, _, _) in thms do\n" ++
  "    for ax in ← NativeTrust.nativeAxiomsOfCore n do\n" ++
  "      IO.println s!\"DEP\\t{i}\\t{ax}\"\n" ++
  "    i := i + 1\n" ++
  "  IO.println \"ENDDEP\"\n"

def checkOptions : String :=
  "set_option Elab.async false\nset_option maxHeartbeats 0\nset_option maxRecDepth 1000000\n" ++
  "set_option nativeTrust.eprint true\n"

def cfgSyntax (split : Nat) : String := s!"(config := \{ split := {split}, trace := true })"

/-- Parse the log of a listing process (`project`: the project's modules; the closure keeps only
those). -/
def parseListing (m : ModName) (project : Std.HashSet String) (txt : String) : ModInfo := Id.run do
  let mut info : ModInfo := { mod := m }
  let mut deps : Std.HashMap Nat (Array String) := {}
  let mut endDep := false
  for l in textLines txt do
    let (tag, cs) := lineFields l
    match tag, cs with
    | "AX", ax :: tac :: inn :: i :: _ =>
      if let some i := i.toNat? then
        let f : Fact := { mod := m, axiomName := ax, tactic := tac, inner := inn == "true", idx := i }
        info := { info with facts := info.facts.push f }
    | "THM", n :: d :: a :: i :: _ =>
      if let some i := i.toNat? then
        let t : Thm := { mod := m, name := n, direct := d.toNat?.getD 0, all := a.toNat?.getD 0, idx := i }
        info := { info with thms := info.thms.push t }
    | "MOD", n :: _ =>
      if project.contains n then info := { info with closure := info.closure.insert n }
    | "DEP", i :: ax :: _ =>
      if let some i := i.toNat? then deps := deps.insert i ((deps.getD i #[]).push ax)
    | "ENDDEP", _ => endDep := true
    | _, _ => pure ()
  if endDep then info := { info with deps := some deps }
  return info

/-- Verdict lines of a supplement log. `byLine`: from the info messages, keyed by source line;
`byName`: from the copies printed at once to standard error (`nativeTrust.eprint`), keyed by
theorem name. Each entry: verdict, kernel theorem, detail, rebuilt statement definitions. -/
def parseSupplement (txt : String) :
    Std.HashMap Nat (String × String × String × String) ×
    Std.HashMap String (String × String × String × String) := Id.run do
  let lines := (textLines txt).toArray
  let mut byLine := {}
  let mut byName := {}
  for h : li in [0:lines.size] do
    let l := lines[li]
    -- `file:line:col: info: VERDICT …` or (standard error) `VERDICT …`
    let (pos?, body) := match l.splitOn ": info: " with
      | pre :: rest@(_ :: _) =>
        match (pre.splitOn ":").reverse with
        | _col :: ln :: _ => (ln.toNat?, ": info: ".intercalate rest)
        | _ => (none, l)
      | _ => (none, l)
    let verdict? := ["KERNELIZED", "REJECTED", "CLEAN"].find? fun v => body.startsWith (v ++ " `")
    let some verdict := verdict? | continue
    -- names between backquotes: the theorem, then (KERNELIZED) the kernel theorem
    let parts := body.splitOn "`"
    let thm := parts[1]?.getD ""
    let kthm := if verdict == "KERNELIZED" then parts[3]?.getD "" else ""
    let next := ((lines[li + 1]?.getD "").splitOn "\n").headD ""
    let next := String.ofList (next.toList.dropWhile (· == ' '))
    let mut detail := ""
    let mut rebuilt := ""
    if verdict == "REJECTED" then
      let rest := "`".intercalate (parts.drop 2)
      detail := String.ofList (rest.toList.dropWhile fun c => c == ':' || c == ' ')
      if next.startsWith "FAIL\t" then
        detail := detail ++ " | " ++ String.ofList (((next.splitOn "\t").drop 3 |> "\t".intercalate).toList.take 400)
    else if verdict == "KERNELIZED" && next.startsWith "OK\t" then
      for f in next.splitOn "\t" do
        if f.startsWith "statement_rebuilt=" then rebuilt := (f.splitOn "=").drop 1 |> "=".intercalate
    let e := (verdict, kthm, detail, rebuilt)
    match pos? with
    | some ln => byLine := byLine.insert ln e
    | none => byName := byName.insert thm e
  return (byLine, byName)

/-- `deps` entries that this run checked and did not prove, with their verdicts. (Facts it did
not check, e.g. from modules outside `--modules` or from dependencies, are left to
`trust_check`, which proves them itself.) -/
def unconvertedDeps (deps : Array String) (lookup : String → Option FactResult) :
    Array String :=
  deps.filterMap fun ax =>
    match lookup ax with
    | some r => if r.verdict == "PROVED" then none
        else some s!"{ax} ({r.verdict}{if r.reason == "" then "" else ":" ++ r.reason})"
    | none => none

def factRowTsv (r : FactResult) : String :=
  joinSep "\t" <| [r.fact.mod.dotted, r.fact.axiomName, r.fact.tactic, toString r.fact.inner,
    r.verdict, r.reason, toString r.secs, r.blockers, r.kernelMs, r.maxrss,
    r.factModule.getD "", r.log].map tsvField

def thmRowTsv (r : ThmRow) : String :=
  joinSep "\t" <| [r.thm.mod.dotted, r.thm.name, r.verdict, r.kernelThm, r.reason,
    toString r.thm.direct, toString r.thm.all, r.detail].map tsvField

def countBy (xs : Array String) : String := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do m := m.insert x (m.getD x 0 + 1)
  let ks := m.toArray.qsort (fun a b => a.1 < b.1)
  return joinSep " " (ks.toList.map fun (k, n) => s!"{k}={n}")

def run (o : Opts) : IO UInt32 := do
  let pkg ← IO.FS.realPath (← IO.currentDir)
  let out := normPath (if (FilePath.mk o.out).isAbsolute then o.out else pkg / o.out)
  let mods_ := out / "mods"
  let logs := out / "logs"
  for d in [out, mods_, logs, out / "gen", out / "Kernel"] do IO.FS.createDirAll d
  let dlog ← SharedLog.new (out / "driver.log")
  let t0 ← IO.monoMsNow
  let lake := (← IO.getEnv "LAKE").getD "lake"
  -- 1. modules whose source mentions native evaluation
  let files ← nativeFiles pkg out
  let mut mods : Array ModName := #[]
  let mut srcOf : Std.HashMap String FilePath := {}
  for f in files do
    if let some m ← moduleOf f (← pkgRootOf f pkg) then
      unless srcOf.contains m.dotted do
        srcOf := srcOf.insert m.dotted f
        mods := mods.push m
  mods := mods.qsort (fun a b => a.dotted < b.dotted)
  if let some sel := o.modules then
    for s in sel do
      unless mods.any (fun m => m.dotted == s || m.esc == s) do
        IO.eprintln s!"ntrust: warning: `{s}` is not a project module that mentions native evaluation"
    mods := mods.filter fun m => sel.contains m.dotted || sel.contains m.esc
  dlog.line s!"start project={pkg} out={out} native_files={files.size} modules={mods.size}"
  IO.println s!"ntrust: {pkg}: {files.size} file(s) mention native evaluation, {mods.size} module(s)"
  -- 2. search path; NativeTrust first
  let projLp ← projectLeanPath lake pkg
  let ntLib ← match o.ntLib with
    | some d =>
      let d := normPath (if (FilePath.mk d).isAbsolute then d else pkg / d)
      unless ← (d / "NativeTrust.olean").pathExists do
        throw (IO.userError s!"--nt-lib {d}: no NativeTrust.olean there")
      pure d.toString
    | none => do
      if let some d ← findIn projLp "NativeTrust.olean" then pure d else
      if !o.skipBuild then
        IO.println s!"ntrust: lake build NativeTrust (log {logs / "build_nt.log"})"
        discard <| runLogged lake #["build", "NativeTrust"] pkg #[] (logs / "build_nt.log")
      match ← findIn projLp "NativeTrust.olean" with
      | some d => pure d
      | none => throw (IO.userError
          "NativeTrust is not on the project's LEAN_PATH: add `require native_trust` to the \
           lakefile, or pass --nt-lib <NativeTrust>/.lake/build/lib/lean")
  let lean ← findLean lake pkg
  let lp := dedup (#[ntLib] ++ projLp ++ #[mods_.toString])
  let env : Array (String × Option String) :=
    #[("LEAN_PATH", some (joinSep ":" lp.toList)), ("LEAN_NUM_THREADS", some "1")]
  let timePre : Array String :=
    if ← (FilePath.mk "/usr/bin/time").pathExists then #["/usr/bin/time", "-f", "maxrss_kb %M"]
    else #[]
  dlog.line s!"lean={lean} nt_lib={ntLib} LEAN_PATH={joinSep ":" lp.toList}"
  -- build the modules without an up-to-date .olean
  let stale (m : ModName) : IO Bool := do
    match ← findIn projLp (m.relPath "olean") with
    | none => return true
    | some d =>
      let some src := srcOf[m.dotted]? | return false
      let so ← src.metadata
      let oo ← (FilePath.mk d / m.relPath "olean").metadata
      return decide (so.modified.sec > oo.modified.sec)
  if !o.skipBuild then
    let todo ← mods.filterM stale
    unless todo.isEmpty do buildModules lake pkg projLp todo logs
  let built ← mods.filterM (hasOlean projLp)
  let notBuilt := mods.filter fun m => !built.contains m
  -- module ids for file names (distinct even when sanitized names coincide)
  let mut ids : Std.HashMap String String := {}
  let mut used : Std.HashSet String := {}
  for m in mods do
    let base := String.ofList ((sanitize (joinSep "_" m.toList)).toList.take 100)
    let mut id := base
    let mut k := 2
    while used.contains id do
      id := s!"{base}_{k}"
      k := k + 1
    used := used.insert id
    ids := ids.insert m.dotted id
  let idOf (m : ModName) : String := ids.getD m.dotted (sanitize m.dotted)
  -- 3. facts, theorems, import closure, per module
  let projectMods : Std.HashSet String := mods.foldl (fun s m => s.insert m.dotted) {}
  let listOne (m : ModName) : IO ModInfo := do
    let src := out / "gen" / s!"list_{idOf m}.lean"
    let log := logs / s!"list_{idOf m}.log"
    try
      IO.FS.writeFile src (listingSource m)
      removeIfExists log
      let (rc, _) ← runCapped lean #["-j1", s!"list_{idOf m}.lean"] (out / "gen") env
        { timeout := max 1800 o.factTimeout, memGB := o.factMem } log
      let info := parseListing m projectMods (← readText log)
      return { info with rc, log := log.toString }
    catch e =>
      dlog.line s!"listing error {m.dotted}: {e}"
      return { mod := m, rc := 255, log := log.toString }
  IO.println s!"ntrust: listing the facts of {built.size} module(s)"
  let infos ← parMap o.jobs built listOne
  let closureOf : Std.HashMap String (Std.HashSet String) :=
    infos.foldl (fun acc i => acc.insert i.mod.dotted i.closure) {}
  let inClosure (m src : ModName) : Bool :=
    src == m || ((closureOf.getD m.dotted {}).contains src.dotted)
  let facts := infos.flatMap (·.facts)
  -- 4. one process per fact
  let cfg := cfgSyntax o.split
  let nInner := (facts.filter (·.inner)).size
  let total := facts.size
  let doneRef ← IO.mkRef 0
  let checkFact (phase : Nat) (imports : Array String) (f : Fact) : IO FactResult := do
    let name := s!"F{phase}_{idOf f.mod}_{f.idx}"
    let log := logs / s!"{name}.log"
    try
      IO.FS.writeFile (mods_ / s!"{name}.lean") <|
        s!"import NativeTrust\nimport {f.mod.esc}\n" ++
        String.join (imports.toList.map (s!"import {·}\n")) ++ checkOptions ++
        s!"prove_native_axiom_nth {f.mod.esc} {f.idx} {cfg}\n"
      let olean := mods_ / s!"{name}.olean"
      removeIfExists olean
      removeIfExists log
      let cmd := timePre ++ #[lean, "-j1", "--tstack=1048576", "-o", s!"{name}.olean",
        s!"{name}.lean"]
      let (rc, ms) ← runCapped cmd[0]! (cmd.extract 1 cmd.size) mods_ env
        { timeout := o.factTimeout, memGB := o.factMem } log
      let b ← IO.FS.readBinFile log
      let (verdict, reason) := classify rc b o.factTimeout
      let blockers := (bytesCaptures b "• `").qsort (· < ·) |>.toList.eraseDups
      let res : FactResult :=
        { fact := f, verdict, reason, secs := (ms + 500) / 1000,
          blockers := String.ofList ((joinSep ";" blockers).toList.take 400),
          kernelMs := ((bytesNatAfter? b "kernel_ms=").map toString).getD "",
          maxrss := ((bytesNatAfter? b "maxrss_kb ").map toString).getD "",
          factModule := if verdict == "PROVED" && (← olean.pathExists) then some name else none,
          log := log.toString }
      let k ← doneRef.modifyGet fun k => (k + 1, k + 1)
      dlog.line s!"fact\t{factRowTsv res}"
      IO.println s!"[{k}/{total}] {verdict}{if reason == "" then "" else " " ++ reason} \
        {f.mod.dotted} #{f.idx} {f.axiomName} ({res.secs}s)"
      return res
    catch e =>
      dlog.line s!"fact error {f.axiomName}: {e}"
      return { fact := f, verdict := "ERROR", reason := s!"driver: {e}", log := log.toString }
  IO.println s!"ntrust: {total} native fact(s), {nInner} inside definitions (phase 1)"
  let r1 ← parMap o.jobs (facts.filter (·.inner)) (checkFact 1 #[])
  -- phase-1 modules of proved inner facts, by the module that declares the fact
  let proved1 := r1.filterMap fun r =>
    if r.verdict == "PROVED" then r.factModule.map (r.fact.mod, ·) else none
  let r2 ← parMap o.jobs (facts.filter (!·.inner)) fun f =>
    checkFact 2 (proved1.filterMap fun (src, fm) => if inClosure f.mod src then some fm else none) f
  let results := r1 ++ r2
  -- 5. report.tsv
  let mut factRows : Array FactResult := results.qsort fun a b =>
    a.fact.mod.dotted < b.fact.mod.dotted ||
      (a.fact.mod.dotted == b.fact.mod.dotted && a.fact.idx < b.fact.idx)
  let stub (m : ModName) (v reason log : String) : FactResult :=
    { fact := { mod := m, axiomName := "-", tactic := "", inner := false, idx := 0 },
      verdict := v, reason, log }
  for m in notBuilt do
    factRows := factRows.push (stub m "NOT_BUILT" "" (logs / "build.log").toString)
  for i in infos do
    if i.facts.isEmpty && i.rc != 0 then
      factRows := factRows.push (stub i.mod "LIST_ERROR" s!"rc{i.rc}" i.log)
  IO.FS.writeFile (out / "report.tsv") <|
    "module\taxiom\ttactic\tinner\tverdict\treason\tseconds\tblockers\tkernel_ms\tmaxrss_kb\t\
     fact_module\tlog\n" ++ String.join (factRows.toList.map (factRowTsv · ++ "\n"))
  -- 6. kernel supplement
  let byAxiom : Std.HashMap String (Array FactResult) :=
    results.foldl (fun acc r => acc.insert r.fact.axiomName ((acc.getD r.fact.axiomName #[]).push r)) {}
  let lookupFor (m : ModName) (ax : String) : Option FactResult :=
    (byAxiom.getD ax #[]).find? fun r => inClosure m r.fact.mod
  let mut thmRows : Array ThmRow := #[]
  let mut jobs : Array (ModName × Array Thm × Array String) := #[]
  for i in infos do
    if i.thms.isEmpty then continue
    let mut todo := #[]
    -- theorems with a fact that this run did not check go last: `trust_check` proves such facts
    -- itself, which can take long, and a process stopped there loses only the later verdicts
    let mut todoLast := #[]
    let mut needed : Array String := #[]
    for t in i.thms do
      match i.deps with
      | some deps =>
        let ds := deps.getD t.idx #[]
        let bad := unconvertedDeps ds (lookupFor i.mod)
        if bad.isEmpty then
          if ds.all fun ax => ((lookupFor i.mod ax).bind (·.factModule)).isSome then
            todo := todo.push t
          else
            todoLast := todoLast.push t
          for ax in ds do
            if let some fm := (lookupFor i.mod ax).bind (·.factModule) then
              unless needed.contains fm do needed := needed.push fm
        else
          let row : ThmRow :=
            { thm := t, verdict := "REJECTED", reason := "fact_not_converted",
              detail := String.ofList ((joinSep "; " bad.toList).toList.take 600) }
          thmRows := thmRows.push row
      | none =>
        todo := todo.push t
    todo := todo ++ todoLast
    if i.deps.isNone then
      needed := results.filterMap fun r => if inClosure i.mod r.fact.mod then r.factModule else none
    unless todo.isEmpty do jobs := jobs.push (i.mod, todo, needed.qsort (· < ·))
  /- Compile `OUT/Kernel/<m>.lean` running `trust_check_nth` on `thms`; the verdicts, and whether
  the module was written (`lean -o` writes nothing when a command fails or the process dies). -/
  let compileSupp (m : ModName) (thms : Array Thm) (imports : Array String) (tag : String) :
      IO (Array ThmRow × Bool) := do
    let relLean := FilePath.mk "Kernel" / m.relPath "lean"
    let relOlean := FilePath.mk "Kernel" / m.relPath "olean"
    let log := logs / s!"kernel_{idOf m}{tag}.log"
    if let some p := (out / relLean).parent then IO.FS.createDirAll p
    let header := #["import NativeTrust", s!"import {m.esc}"] ++ imports.map (s!"import {·}") ++
      (checkOptions.splitOn "\n" |>.filter (· != "")).toArray
    let mut lines := header
    let mut lineOf : Std.HashMap Nat Nat := {}
    for t in thms do
      lines := lines.push s!"trust_check_nth {m.esc} {t.idx} {cfg}"
      lineOf := lineOf.insert t.idx lines.size
    IO.FS.writeFile (out / relLean) (joinSep "\n" lines.toList ++ "\n")
    removeIfExists (out / relOlean)
    removeIfExists log
    let cmd := timePre ++ #[lean, "-j1", "--tstack=1048576", "-o", relOlean.toString,
      relLean.toString]
    IO.println s!"ntrust: supplement {relLean} ({thms.size} theorem(s)\
      {if tag == "" then "" else ", again with the kernelized ones only"})"
    let (rc, ms) ← runCapped cmd[0]! (cmd.extract 1 cmd.size) out env
      { timeout := o.kernelTimeout, memGB := o.factMem } log
    let txt ← readText log
    let (byLine, byName) := parseSupplement txt
    let firstErr := ((textLines txt).find? fun l => (l.splitOn ": error: ").length > 1).getD ""
    let rows := thms.map fun t =>
      let e? := (lineOf[t.idx]?.bind fun ln => byLine[ln]?) <|> byName[t.name]?
      match e? with
      | some (v, kthm, detail, rebuilt) =>
        { thm := t, verdict := v, kernelThm := kthm, reason := "trust_check", detail,
          statementRebuilt := rebuilt }
      | none =>
        { thm := t, verdict := if rc == 124 then "TIMEOUT" else "ERROR",
          reason := if rc == 124 then s!"{o.kernelTimeout}s" else s!"rc{rc}",
          detail := s!"no verdict in {log}{if firstErr == "" then "" else ": " ++ firstErr}" }
    let written ← (out / relOlean).pathExists
    -- the kernel theorems exist only if the supplement module was written
    let rows := if written then rows else rows.map fun r => if r.verdict != "KERNELIZED" then r else
      { r with verdict := "ERROR", reason := s!"rc{rc}",
               detail := s!"KERNELIZED by trust_check, but {relOlean} was not written ({log})" }
    dlog.line s!"supplement {m.dotted}{tag} rc={rc} secs={ms / 1000} written={written} \
      kernelized={(rows.filter (·.verdict == "KERNELIZED")).size}/{rows.size}"
    return (rows, written)
  /- One supplement module; if it was not written (a process that died at one theorem, say),
  once more with only the theorems that `trust_check` kernelized, so that they persist. -/
  let suppOne (job : ModName × Array Thm × Array String) : IO (Array ThmRow) := do
    let (m, thms, imports) := job
    try
      let (rows, written) ← compileSupp m thms imports ""
      if written then return rows
      let good := rows.filter (·.detail.startsWith "KERNELIZED by trust_check") |>.map (·.thm)
      if good.isEmpty || good.size == thms.size then return rows
      let (rows2, _) ← compileSupp m good imports "_retry"
      return rows.map fun r => (rows2.find? (·.thm.idx == r.thm.idx)).getD r
    catch e =>
      return thms.map fun t => { thm := t, verdict := "ERROR", reason := s!"driver: {e}" }
  let suppRows ← parMap o.jobs jobs suppOne
  thmRows := (thmRows ++ suppRows.flatten).qsort fun a b =>
    a.thm.mod.dotted < b.thm.mod.dotted ||
      (a.thm.mod.dotted == b.thm.mod.dotted && a.thm.idx < b.thm.idx)
  IO.FS.writeFile (out / "theorems.tsv") <|
    "module\ttheorem\tverdict\tkernel_theorem\treason\tdirect_facts\tall_facts\tdetail\n" ++
    String.join (thmRows.toList.map (thmRowTsv · ++ "\n"))
  let pairs := (thmRows.filter (·.verdict == "KERNELIZED")).toList.map fun r =>
    let reb := (r.statementRebuilt.replace "[" "").replace "]" ""
    let rebs := ((reb.splitOn ",").map (fun s => String.ofList (s.toList.filter (· != ' ')))).filter
      (· != "")
    s!"    \{\"module\": {jsonStr r.thm.mod.esc}, \"theorem\": {jsonStr r.thm.name}, \
      \"kernel_module\": {jsonStr ("Kernel." ++ r.thm.mod.esc)}, \
      \"kernel_theorem\": {jsonStr r.kernelThm}, \"same_statement\": {rebs.isEmpty}, \
      \"statement_rebuilt\": {jsonArr (rebs.map jsonStr)}}"
  IO.FS.writeFile (out / "comparator.json") <|
    "{\n  \"format\": \"ntrust-comparator/1\",\n" ++
    s!"  \"project\": {jsonStr pkg.toString},\n" ++
    s!"  \"lean_path\": {jsonArr ((lp.toList ++ [out.toString]).map jsonStr)},\n" ++
    "  \"permitted_axioms\": [\"propext\", \"Classical.choice\", \"Quot.sound\"],\n" ++
    "  \"pairs\": [\n" ++ joinSep ",\n" pairs ++ (if pairs.isEmpty then "" else "\n") ++ "  ]\n}\n"
  -- summary
  let secs := ((← IO.monoMsNow) - t0) / 1000
  let fv := factRows.map (·.verdict)
  let tv := thmRows.map (·.verdict)
  IO.println s!"ntrust: facts: {results.size} ({countBy fv})"
  IO.println s!"ntrust: theorems: {thmRows.size} ({countBy tv})"
  IO.println s!"ntrust: supplement: {jobs.size} module(s) in {out / "Kernel"}; \
    {pairs.length} kernel theorem(s) in {out / "comparator.json"}"
  IO.println s!"ntrust: reports: {out / "report.tsv"}, {out / "theorems.tsv"} ({secs}s)"
  dlog.line s!"end facts {countBy fv} theorems {countBy tv} secs={secs}"
  let allGood := fv.all (· == "PROVED") && tv.all (· == "KERNELIZED")
  return if allGood then 0 else 1

end NativeTrust.Driver

open NativeTrust.Driver in
def main (args : List String) : IO UInt32 := do
  if args.head? == some "migrate" then
    return ← NativeTrust.Driver.Migrate.main args.tail
  match parseArgs args {} with
  | .error e =>
    IO.eprintln s!"ntrust: {e}\n\n{usage}"
    return 2
  | .ok o =>
    if o.help then
      IO.println usage
      return 0
    try run o catch e =>
      IO.eprintln s!"ntrust: error: {e}"
      return (2 : UInt32)
