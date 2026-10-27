import NativeTrust.Driver.Project

/-!
# `ntrust migrate`: replace unnecessary `native_decide` by `decide +kernel`

```
lake exe ntrust migrate [--report FILE] [--dry-run] [--jobs N] [--rounds N] [--round-timeout S]
                        [--build-timeout S] [--mem GB] [--build-mem GB] [--census-batch N]
                        [--no-unknown] [--skip-final-build] [--out DIR] [--restore]
```

Typical use: `lake exe ntrust --split 1` (per-fact verdicts in `.ntrust/report.tsv`), then
`lake exe ntrust migrate --report .ntrust/report.tsv`, then `git diff` (or
`.ntrust/migrate/migrate.patch`) and `.ntrust/migrate/summary.json`.

Run in the root of a Lake project (built, or buildable). The project's sources are rewritten IN
PLACE (review the result with `git diff`); originals of every touched file are kept in
`OUT/migrate/orig/` (`--restore` puts them back; an interrupted run is undone automatically at the
next start). Every `native_decide`, `decide +native` and `decide (config := { native := true })`
whose fact Lean's kernel checks becomes `decide +kernel` (`kernel := true`); `bv_decide` and
occurrences inside `macro`/`syntax`/`elab` definitions or syntax quotations are never touched.

1. **Census** (needs no NativeTrust library, only the project's `lean` and `LEAN_PATH`): a
   generated core-Lean file per batch of built project modules lists every native axiom
   `<decl>._native.<tactic>.ax_…` with its declaration range (Lean records the range of the
   tactic call, so every fact maps to one source occurrence), and every declaration whose
   dependency closure contains a native axiom.
2. **Plan**: the sources are lexed (comments, strings and character literals skipped). An
   occurrence is rewritten when every fact it produced is `PROVED` in `--report FILE` (the
   `report.tsv` of `lake exe ntrust --split 1`, or a per-fact `.ax.tsv` of the study driver; a
   run with `wf := false` gives exactly the facts that plain kernel evaluation proves). Without
   a report every occurrence is tried and the build decides. Occurrences that left no fact in
   the `.olean`s (`example`s) are tried too, unless `--no-unknown`.
3. **Build rounds**: `lake build` of the rewritten modules; each `error: file:line:col:` is
   attributed to an occurrence (same column span, else same line, else the enclosing
   declaration, else the whole file) and that occurrence is reverted; modules still elaborating
   at `--round-timeout` get their untested occurrences reverted. Repeat (`--rounds`). A `lean`
   process that cannot create a thread (an address-space cap, `--build-mem`, below what its
   elaboration threads reserve) is an environment failure, not a verdict: the build is repeated,
   and only in the last round are such modules' occurrences reverted.
4. **Verification**: `lake build` of every module that was built before (the rewritten modules
   and everything downstream), then the census again: native axioms and native-dependent
   declarations before/after, and for each rewritten declaration whether it still depends on a
   native axiom (and why).

Outputs in `OUT/migrate/` (default `OUT` = `.ntrust`): `plan.tsv` (a line per occurrence: file,
line, column, form, status, reason, facts), `summary.json`, `migrate.patch` (unified diff,
original vs rewritten), `census_before/`, `census_after/`, `build_*.log`. Exit code 0 iff the
final build succeeded (with `--dry-run`: census and plan only, nothing rewritten, exit 0).
-/

namespace NativeTrust.Driver.Migrate

open System NativeTrust.Driver

structure MOpts where
  report : Option String := none
  jobs : Nat := 4
  rounds : Nat := 5
  roundTimeout : Nat := 900
  buildTimeout : Nat := 7200
  mem : Nat := 48
  buildMem : Nat := 0
  batch : Nat := 40
  noUnknown : Bool := false
  dryRun : Bool := false
  restore : Bool := false
  skipFinal : Bool := false
  out : String := ".ntrust"
  help : Bool := false

def usage : String :=
"usage: lake exe ntrust migrate [options]     (in the root directory of a Lake project)

Rewrites the project's sources IN PLACE: every native_decide / decide +native whose fact Lean's
kernel checks becomes decide +kernel. Verifies that the project still builds and counts the native
axioms before and after. Originals are kept in OUT/migrate/orig/.

options:
  --report FILE       per-fact verdicts (report.tsv of `lake exe ntrust --split 1`, or a .ax.tsv):
                      only occurrences whose facts are all PROVED are rewritten
                      (default: every occurrence is tried and the build decides)
  --dry-run           census and plan only (OUT/migrate/plan.tsv); nothing is rewritten
  --jobs N            parallel lean processes (census, and LEAN_NUM_THREADS of lake) (default 4)
  --rounds N          rewrite/build/revert rounds (default 5)
  --round-timeout S   time limit of one build round, seconds (default 900)
  --build-timeout S   time limit of the final build, seconds (default 7200)
  --mem GB            address-space cap per census process, GB (default 48)
  --build-mem GB      address-space cap per process of the lake builds, GB (default 0: none;
                      a lean process with many elaboration threads can need over 40 GB of
                      address space, so small caps make builds fail with \"failed to create
                      thread\"; such builds are retried 3 times)
  --census-batch N    modules per census process (default 40)
  --no-unknown        do not try occurrences that left no fact in the .oleans (examples)
  --skip-final-build  do not rebuild every previously built module at the end
  --out DIR           output directory (default .ntrust); results in DIR/migrate
  --restore           put back the originals saved by the last run (DIR/migrate/orig) and exit
  -h, --help          this text

Exit code 0: the rewritten project builds; 1: it does not; 2: usage or setup error."

partial def parseArgs : List String → MOpts → Except String MOpts
  | [], o => .ok o
  | a :: rest, o =>
    match a.splitOn "=" with
    | k :: v :: vs =>
      if k.startsWith "--" then parseArgs (k :: "=".intercalate (v :: vs) :: rest) o
      else .error s!"unexpected argument `{a}`"
    | _ =>
      let nat (k : String) (f : Nat → MOpts) : Except String MOpts :=
        match rest with
        | v :: rest' =>
          match v.toNat? with
          | some n => parseArgs rest' (f n)
          | none => .error s!"{k} expects a number, got `{v}`"
        | [] => .error s!"{k} expects a value"
      let str (k : String) (f : String → MOpts) : Except String MOpts :=
        match rest with
        | v :: rest' => parseArgs rest' (f v)
        | [] => .error s!"{k} expects a value"
      match a with
      | "--report" => str a fun v => { o with report := some v }
      | "--jobs" => nat a fun n => { o with jobs := max 1 n }
      | "--rounds" => nat a fun n => { o with rounds := max 1 n }
      | "--round-timeout" => nat a fun n => { o with roundTimeout := max 1 n }
      | "--build-timeout" => nat a fun n => { o with buildTimeout := max 1 n }
      | "--mem" => nat a fun n => { o with mem := max 1 n }
      | "--build-mem" => nat a fun n => { o with buildMem := n }
      | "--census-batch" => nat a fun n => { o with batch := max 1 n }
      | "--out" => str a fun v => { o with out := v }
      | "--no-unknown" => parseArgs rest { o with noUnknown := true }
      | "--dry-run" => parseArgs rest { o with dryRun := true }
      | "--restore" => parseArgs rest { o with restore := true }
      | "--skip-final-build" => parseArgs rest { o with skipFinal := true }
      | "-h" | "--help" => parseArgs rest { o with help := true }
      | _ => .error s!"unknown option `{a}`"

/-! ## Census (a core-Lean script run by the project's `lean`) -/

/-- The census script; `@@IMPORTS@@`, `@@OUT@@` and `@@MODS@@` are filled in per batch. -/
def censusTemplate : String := r##"import Lean
@@IMPORTS@@
/-! ntrust migrate census (generated): native axioms with their declaration ranges, and the
declarations whose dependency closure contains a native axiom. -/
open Lean

namespace NTMigrateCensus

def isNativeAx (env : Environment) (n : Name) : Bool :=
  n.components.contains `_native && (env.find? n matches some (.axiomInfo _))

def rng (r? : Option DeclarationRanges) : String :=
  match r? with
  | some r => s!"{r.range.pos.line}:{r.range.pos.column}:{r.range.endPos.line}:{r.range.endPos.column}"
  | none => "-"

def internalComp : Name → Bool
  | .str p s => s.startsWith "_" || internalComp p
  | .num p _ => internalComp p
  | .anonymous => false

def isUser (n : Name) : Bool := !internalComp (privateToUserName n)

def parentOf (n : Name) : Name :=
  (n.components.takeWhile (· != `_native)).foldl (· ++ ·) .anonymous

partial def rangeUp (n : Name) : CoreM (Name × Option DeclarationRanges) := do
  match ← findDeclarationRanges? n with
  | some r => return (n, some r)
  | none =>
    match n with
    | .str p _ | .num p _ => if p.isAnonymous then return (n, none) else rangeUp p
    | .anonymous => return (n, none)

def kindOf : ConstantInfo → String
  | .thmInfo _ => "thm" | .defnInfo _ => "def" | .opaqueInfo _ => "opaque" | .axiomInfo _ => "axiom"
  | .inductInfo _ => "induct" | .ctorInfo _ => "ctor" | .recInfo _ => "rec" | .quotInfo _ => "quot"

def valueOf? : ConstantInfo → Option Expr
  | .thmInfo v => some v.value | .defnInfo v => some v.value | .opaqueInfo v => some v.value | _ => none

def usesAny (s : Std.HashSet Name) (e : Expr) : Bool :=
  e.foldConsts false fun c acc => acc || s.contains c

def run (out : System.FilePath) (mods : Array Name) : CoreM Unit := do
  let env ← getEnv
  let mut lines : Array String := #[]
  let names := env.header.moduleNames
  let n := names.size
  let mut idxOf : Std.HashMap Name Nat := {}
  for i in [0:n] do idxOf := idxOf.insert names[i]! i
  let mut nativeMod : Array Bool := Array.replicate n false
  for i in [0:n] do
    for c in env.header.moduleData[i]!.constNames do
      if isNativeAx env c then
        nativeMod := nativeMod.set! i true
        break
  let mut capable : Array Bool := nativeMod
  for _pass in [0:4] do
    let mut changed := false
    for i in [0:n] do
      if capable[i]! then continue
      for imp in env.header.moduleData[i]!.imports do
        if let some j := idxOf[imp.module]? then
          if capable[j]! then
            capable := capable.set! i true
            changed := true
            break
    if !changed then break
  let mut dirty : Std.HashSet Name := {}
  for _pass in [0:6] do
    let mut changed := false
    for i in [0:n] do
      if !capable[i]! then continue
      for c in env.header.moduleData[i]!.constNames do
        if dirty.contains c then continue
        if isNativeAx env c then
          dirty := dirty.insert c; changed := true; continue
        let some ci := env.find? c | continue
        let hit := usesAny dirty ci.type || match valueOf? ci with
          | some v => usesAny dirty v
          | none => false
        if hit then
          dirty := dirty.insert c; changed := true
    if !changed then break
  for m in mods do
    if !idxOf.contains m then
      lines := lines.push s!"NOMOD\t{m}"
      continue
    let i := idxOf[m]!
    let mut nAx := 0
    let mut nUser := 0
    let mut nDirty := 0
    for c in env.header.moduleData[i]!.constNames do
      if isNativeAx env c then
        nAx := nAx + 1
        let cs := c.components
        let tac := (cs.dropWhile (· != `_native)).drop 1 |>.headD .anonymous
        let axr ← findDeclarationRanges? c
        let (p, pr) ← rangeUp (parentOf c)
        lines := lines.push s!"AX\t{m}\t{c}\t{tac}\t{rng axr}\t{p}\t{rng pr}"
        continue
      let some ci := env.find? c | continue
      if !isUser c then continue
      match ci with
      | .thmInfo _ | .defnInfo _ | .opaqueInfo _ =>
        nUser := nUser + 1
        if dirty.contains c then
          nDirty := nDirty + 1
          let (p, pr) ← rangeUp c
          lines := lines.push s!"DIRTY\t{m}\t{c}\t{kindOf ci}\t{p}\t{rng pr}"
      | _ => pure ()
    lines := lines.push s!"MOD\t{m}\t{nAx}\t{nUser}\t{nDirty}\t{if capable[i]! then 1 else 0}"
  IO.FS.writeFile out ("\n".intercalate lines.toList ++ "\nEND\n")

end NTMigrateCensus

set_option maxHeartbeats 0 in
#eval NTMigrateCensus.run @@OUT@@ #[@@MODS@@]
"##

/-- A range `line:col:endLine:endCol` (columns in code points). -/
abbrev Rng := Nat × Nat × Nat × Nat

def parseRng (s : String) : Option Rng :=
  match (s.splitOn ":").map String.toNat? with
  | [some a, some b, some c, some d] => some (a, b, c, d)
  | _ => none

structure AxRow where
  module : String
  axiomName : String
  tactic : String
  range : Option Rng
  parent : String
  prange : Option Rng

structure DirtyRow where
  module : String
  decl : String
  kind : String
  parent : String
  prange : Option Rng

structure Census where
  ax : Array AxRow := #[]
  dirty : Array DirtyRow := #[]
  /-- module ↦ (native axioms, user declarations, native-dependent user declarations) -/
  mods : Std.HashMap String (Nat × Nat × Nat) := {}
  failed : Array String := #[]

/-- Module name as Lean prints it (`A.«389»`) to the dotted file-derived form (`A.389`). -/
def unescMod (m : String) : String := (m.replace "«" "").replace "»" ""

def Census.parseLines (c : Census) (lines : List String) : Census := Id.run do
  let mut c := c
  for l in lines do
    match l.splitOn "\t" with
    | ["AX", m, a, t, r, p, pr] =>
      c := { c with ax := c.ax.push { module := unescMod m, axiomName := a, tactic := t, range := parseRng r,
                                      parent := p, prange := parseRng pr } }
    | ["DIRTY", m, d, k, p, pr] =>
      c := { c with dirty := c.dirty.push { module := unescMod m, decl := d, kind := k, parent := p,
                                            prange := parseRng pr } }
    | ["MOD", m, a, u, d, _] =>
      c := { c with mods := c.mods.insert (unescMod m) (a.toNat?.getD 0, u.toNat?.getD 0, d.toNat?.getD 0) }
    | _ => pure ()
  return c

/-- Run the census over `mods` in batches of `batch` modules, at most `jobs` processes at a time;
a batch whose process fails is split in halves (a module that fails alone is recorded). -/
def runCensus (lean : String) (lp : Array String) (dir : FilePath) (mods : Array ModName)
    (jobs batch mem : Nat) : IO Census := do
  IO.FS.createDirAll dir
  let counter ← IO.mkRef 0
  let env : Array (String × Option String) :=
    #[("LEAN_PATH", some (joinSep ":" lp.toList)), ("LEAN_NUM_THREADS", some "1")]
  let rec one (fuel : Nat) (b : Array ModName) : IO (List String × Array String) := do
    let k ← counter.modifyGet fun k => (k, k + 1)
    let src := dir / s!"C{k}.lean"
    let out := dir / s!"C{k}.tsv"
    let log := dir / s!"C{k}.log"
    for p in [out, log] do
      if ← p.pathExists then IO.FS.removeFile p
    let text := ((censusTemplate.replace "@@IMPORTS@@"
        (String.join (b.toList.map fun m => s!"import {m.esc}\n"))).replace "@@OUT@@"
        out.toString.quote).replace "@@MODS@@" (joinSep ", " (b.toList.map (·.nameTerm)))
    IO.FS.writeFile src text
    discard <| runCapped lean #["-j1", src.toString] dir env { timeout := 3600, memGB := mem } log
    let res ← readText out
    let ok := (res.splitOn "\nEND").length > 1 || res.startsWith "END"
    if ok then return (textLines res, #[])
    match fuel with
    | 0 => return ([], b.map (·.dotted))
    | fuel + 1 =>
      if b.size ≤ 1 then return ([], b.map (·.dotted))
      let h := b.size / 2
      let (l1, f1) ← one fuel (b.extract 0 h)
      let (l2, f2) ← one fuel (b.extract h b.size)
      return (l1 ++ l2, f1 ++ f2)
  let mut batches : Array (Array ModName) := #[]
  let mut i := 0
  while i < mods.size do
    batches := batches.push (mods.extract i (i + batch))
    i := i + batch
  let results ← parMap jobs batches (one 64)
  let mut c : Census := {}
  for (lines, failed) in results do
    c := c.parseLines lines
    c := { c with failed := c.failed ++ failed }
  return c

/-! ## Lexing -/

def isLetterLike (c : Char) : Bool :=
  let v := c.toNat
  (0x3b1 ≤ v && v ≤ 0x3c9 && v != 0x3bb) || (0x391 ≤ v && v ≤ 0x3A9 && v != 0x3A0 && v != 0x3A3) ||
  (0x3ca ≤ v && v ≤ 0x3fb) || (0x1f00 ≤ v && v ≤ 0x1ffe) || (0x2100 ≤ v && v ≤ 0x214f) ||
  (0x1d49c ≤ v && v ≤ 0x1d59f) || (0x2080 ≤ v && v ≤ 0x209c) || (0x1d62 ≤ v && v ≤ 0x1d6a)

/-- A character that can continue a Lean identifier. -/
def isIdc (c : Char) : Bool :=
  c.isAlphanum || c == '_' || c == '\'' || c == '!' || c == '?' || isLetterLike c

def isWordChar (c : Char) : Bool := c.isAlphanum || c == '_' || isLetterLike c

def isHex (c : Char) : Bool := c.isDigit || ('a' ≤ c && c ≤ 'f') || ('A' ≤ c && c ≤ 'F')

def at? (t : Array Char) (i : Nat) : Char := t.getD i '\x00'

/-- End (exclusive) of a character literal starting at `i` (`t[i] = '\''`). -/
def charLitEnd? (t : Array Char) (i : Nat) : Option Nat :=
  if at? t (i + 1) == '\\' then
    let c := at? t (i + 2)
    if c == 'x' && isHex (at? t (i + 3)) && isHex (at? t (i + 4)) && at? t (i + 5) == '\'' then
      some (i + 6)
    else if c == 'u' && isHex (at? t (i + 3)) && isHex (at? t (i + 4)) && isHex (at? t (i + 5)) &&
        isHex (at? t (i + 6)) && at? t (i + 7) == '\'' then
      some (i + 8)
    else if i + 2 < t.size && c != '\n' && at? t (i + 3) == '\'' then some (i + 4)
    else none
  else
    let c := at? t (i + 1)
    if i + 1 < t.size && c != '\'' && c != '\\' && c != '\n' && at? t (i + 2) == '\'' then
      some (i + 3)
    else none

/-- `1` at every character that is code (not in a comment, string or character literal). -/
def codeMask (t : Array Char) : ByteArray := Id.run do
  let n := t.size
  let mut mask := ByteArray.mk (Array.replicate n 0)
  let mut i := 0
  while i < n do
    let c := t[i]!
    if c == '-' && at? t (i + 1) == '-' then
      let mut j := i
      while j < n && t[j]! != '\n' do j := j + 1
      i := j
    else if c == '/' && at? t (i + 1) == '-' then
      let mut depth := 1
      let mut j := i + 2
      while j < n && depth > 0 do
        if t[j]! == '/' && at? t (j + 1) == '-' then
          depth := depth + 1
          j := j + 2
        else if t[j]! == '-' && at? t (j + 1) == '/' then
          depth := depth - 1
          j := j + 2
        else
          j := j + 1
      i := j
    else if c == '"' then
      let mut j := i + 1
      while j < n && t[j]! != '"' do
        j := j + (if t[j]! == '\\' then 2 else 1)
      i := j + 1
    else if c == '\'' && (i == 0 || !isIdc t[i - 1]!) && (charLitEnd? t i).isSome then
      i := (charLitEnd? t i).getD (i + 1)
    else
      mask := mask.set! i 1
      i := i + 1
  return mask

def lineStarts (t : Array Char) : Array Nat := Id.run do
  let mut ls := #[0]
  for i in [0:t.size] do
    if t[i]! == '\n' then ls := ls.push (i + 1)
  return ls

/-- (line from 1, column from 0 in code points) of offset `off`. -/
def posOf (ls : Array Nat) (off : Nat) : Nat × Nat := Id.run do
  let mut lo := 0
  let mut hi := ls.size - 1
  while lo < hi do
    let mid := (lo + hi + 1) / 2
    if ls[mid]! ≤ off then lo := mid else hi := mid - 1
  return (lo + 1, off - ls[lo]!)

def hasAt (t : Array Char) (i : Nat) (s : String) : Bool := Id.run do
  let cs := s.toList.toArray
  if i + cs.size > t.size then return false
  for j in [0:cs.size] do
    if t[i + j]! != cs[j]! then return false
  return true

def containsStr (t : Array Char) (s : String) : Bool := Id.run do
  for i in [0:t.size] do
    if hasAt t i s then return true
  return false

def skipSpace (t : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < t.size && t[j]!.isWhitespace do j := j + 1
  return j

/-- `kw` at `i`, not followed by a word character. -/
def keywordAt (t : Array Char) (i : Nat) (kw : String) : Bool :=
  hasAt t i kw && !isWordChar (at? t (i + kw.length))

/-- The command text `cmd` (from the start of the command to the occurrence) begins a
macro/syntax/elab-like command (optional attribute and modifiers first). -/
def startsMacroCommand (cmd : Array Char) : Bool := Id.run do
  let mut i := 0
  if hasAt cmd 0 "@[" then
    let mut j := 2
    while j < cmd.size && cmd[j]! != ']' do j := j + 1
    if j < cmd.size then i := skipSpace cmd (j + 1)
  let mods := ["private", "protected", "scoped", "local", "noncomputable", "partial", "unsafe"]
  let mut progress := true
  while progress do
    progress := false
    for m in mods do
      if hasAt cmd i m && (at? cmd (i + m.length)).isWhitespace then
        i := skipSpace cmd (i + m.length)
        progress := true
        break
  let kws := ["macro", "macro_rules", "syntax", "elab", "elab_rules", "notation", "infix", "infixl",
    "infixr", "prefix", "postfix", "meta", "initialize", "builtin_initialize"]
  return kws.any (keywordAt cmd i ·)

/-- The occurrence at `off` lies in a macro/syntax/elab definition or a syntax quotation. -/
def inMacroContext (t : Array Char) (ls : Array Nat) (off : Nat) : Bool := Id.run do
  let (line, _) := posOf ls off
  let mut k := line - 1
  let lineBlank (k : Nat) : Bool := Id.run do
    let s := ls[k]!
    let e := if k + 1 < ls.size then ls[k + 1]! else t.size
    for j in [s:e] do
      if !t[j]!.isWhitespace then return false
    return true
  while k > 0 && (k ≥ ls.size || lineBlank k || at? t ls[k]! == ' ' || at? t ls[k]! == '\t') do
    k := k - 1
  let cmd := t.extract ls[k]! off
  return startsMacroCommand cmd || containsStr cmd "`(" || containsStr cmd "(tactic|" ||
    containsStr cmd "(tacticSeq|"

structure Occ where
  id : Nat := 0
  file : String
  start : Nat
  stop : Nat
  line : Nat
  col : Nat
  form : String
  old : String
  new : String
  inMacro : Bool
  module : String := ""
  facts : Array String := #[]
  status : String := "rewrite"
  reason : String := ""
  newCol : Nat := 0
  newEnd : Nat := 0
  deriving Inhabited

def substr (t : Array Char) (a b : Nat) : String := String.ofList (t.extract a b).toList

def replaceAll (s pat rep : String) : String := s.replace pat rep

/-- `+native` (as a whole word) in a decide configuration text. -/
def hasPlusNative (cfg : String) : Bool := Id.run do
  let t := cfg.toList.toArray
  for i in [0:t.size] do
    if hasAt t i "+native" && !isWordChar (at? t (i + 7)) then return true
  return false

/-- `native := true` (spaces optional) in a configuration text; returns the text with
`kernel := true` instead, keeping the spacing. -/
def nativeTrueToKernel? (cfg : String) : Option String := Id.run do
  let t := cfg.toList.toArray
  for i in [0:t.size] do
    if hasAt t i "native" && (i == 0 || !isWordChar t[i - 1]!) then
      let j := i + 6
      let mut k := j
      while k < t.size && (t[k]! == ' ' || t[k]! == '\t') do k := k + 1
      if hasAt t k ":=" then
        let mut l := k + 2
        while l < t.size && (t[l]! == ' ' || t[l]! == '\t') do l := l + 1
        if hasAt t l "true" && !isWordChar (at? t (l + 4)) then
          return some (substr t 0 i ++ "kernel" ++ substr t j t.size)
  return none

/-- The decide configuration after `decide` at `i` (items `+opt`, `-opt`, `(config := { … })`,
`(opt := …)`, separated by spaces or tabs): its end offset. -/
def decideCfgEnd (t : Array Char) (i : Nat) : Nat := Id.run do
  let mut j := i
  let mut done := false
  while !done do
    let mut k := j
    while k < t.size && (t[k]! == ' ' || t[k]! == '\t') do k := k + 1
    let c := at? t k
    if (c == '+' || c == '-') && ((at? t (k + 1)).isAlpha || at? t (k + 1) == '_') then
      let mut e := k + 2
      while e < t.size && ((t[e]!).isAlphanum || t[e]! == '_') do e := e + 1
      j := e
    else if c == '(' then
      -- `(config := { … })` without nested braces/parentheses, or `(ident := …)` without parens
      let mut e := k + 1
      let mut ok := false
      if hasAt t e "config" then
        let mut f := e + 6
        while f < t.size && (t[f]! == ' ' || t[f]! == '\t') do f := f + 1
        if hasAt t f ":=" then
          f := f + 2
          while f < t.size && (t[f]! == ' ' || t[f]! == '\t') do f := f + 1
          if at? t f == '{' then
            let mut g := f + 1
            while g < t.size && !(t[g]! == '{' || t[g]! == '}' || t[g]! == '(' || t[g]! == ')') do
              g := g + 1
            if at? t g == '}' && at? t (g + 1) == ')' then
              e := g + 2
              ok := true
      if !ok && ((at? t e).isAlpha || at? t e == '_') then
        let mut f := e + 1
        while f < t.size && ((t[f]!).isAlphanum || t[f]! == '_') do f := f + 1
        while f < t.size && (t[f]! == ' ' || t[f]! == '\t') do f := f + 1
        if hasAt t f ":=" then
          let mut g := f + 2
          while g < t.size && t[g]! != '(' && t[g]! != ')' do g := g + 1
          if at? t g == ')' then
            e := g + 1
            ok := true
      if ok then j := e else done := true
    else
      done := true
  return j

/-- Occurrences of `native_decide`, `decide +native` and `decide (… native := true …)` in code. -/
def occurrencesIn (rel : String) (text : String) : Array Occ := Id.run do
  let t := text.toList.toArray
  if !(containsStr t "native") then return #[]
  let mask := codeMask t
  let ls := lineStarts t
  let mut out : Array Occ := #[]
  for i in [0:t.size] do
    if mask[i]! == 0 then continue
    if t[i]! == 'n' && hasAt t i "native_decide" then
      let prev := if i == 0 then ' ' else t[i - 1]!
      let nxt := at? t (i + 13)
      if isIdc prev || prev == '.' || prev == '`' || prev == '«' || isIdc nxt then continue
      let (line, col) := posOf ls i
      out := out.push { file := rel, start := i, stop := i + 13, line, col, form := "native_decide",
                        old := "native_decide", new := "decide +kernel",
                        inMacro := inMacroContext t ls i }
    else if t[i]! == 'd' && hasAt t i "decide" then
      let prev := if i == 0 then ' ' else t[i - 1]!
      if isIdc prev || prev == '.' || prev == '`' || prev == '«' || isIdc (at? t (i + 6)) then continue
      let e := decideCfgEnd t (i + 6)
      if e == i + 6 then continue
      let cfg := substr t (i + 6) e
      let (form, newCfg?) :=
        if hasPlusNative cfg then
          -- replace each whole-word `+native`
          let cs := cfg.toList.toArray
          let rec go (k : Nat) (acc : String) (fuel : Nat) : String :=
            match fuel with
            | 0 => acc
            | fuel + 1 =>
              if k ≥ cs.size then acc
              else if hasAt cs k "+native" && !isWordChar (at? cs (k + 7)) then
                go (k + 7) (acc ++ "+kernel") fuel
              else go (k + 1) (acc.push cs[k]!) fuel
          ("decide +native", some (go 0 "" (cs.size + 1)))
        else match nativeTrueToKernel? cfg with
          | some c => ("decide (native := true)", some c)
          | none => ("", none)
      let some newCfg := newCfg? | continue
      let (line, col) := posOf ls i
      out := out.push { file := rel, start := i, stop := e, line, col, form,
                        old := substr t i e, new := "decide" ++ newCfg,
                        inMacro := inMacroContext t ls i }
  return out.qsort (fun a b => a.start < b.start)

/-! ## Reports -/

/-- Last verdict per axiom: `report.tsv` of `lake exe ntrust` (header `module axiom …`, verdict in
column 5) or a study `.ax.tsv` (axiom in column 3, verdict in column 6). -/
def loadReport (p : FilePath) : IO (Std.HashMap String (String × String)) := do
  let txt ← readText p
  let lines := textLines txt
  let isNtrust := match lines.head? with
    | some h => h.startsWith "module\taxiom"
    | none => false
  let mut out : Std.HashMap String (String × String) := {}
  for l in lines do
    let c := (l.splitOn "\t").toArray
    if isNtrust then
      if c.size ≥ 6 && c[0]! != "module" && c[1]! != "-" then
        out := out.insert c[1]! (c[4]!, c[5]!)
    else if c.size ≥ 7 && c[2]! != "-" && c[2]! != "" then
      out := out.insert c[2]! (c[5]!, c[6]!)
  return out

/-! ## Building -/

/-- One sample of the `lean` processes whose working directory lies under `root`: their source
file ↦ (first, last) time seen, in ms since `t0`. -/
def sampleLean (root : String) (t0 : Nat) (seen : IO.Ref (Std.HashMap String (Nat × Nat)))
    (peak : IO.Ref Nat) : IO Unit := do
  let now := (← IO.monoMsNow) - t0
  let entries ← match ← (FilePath.mk "/proc").readDir.toBaseIO with
    | .ok es => pure es
    | .error _ => pure #[]
  let mut n := 0
  for e in entries do
    let digits := e.fileName.toList
    unless !digits.isEmpty && digits.all Char.isDigit do continue
    let base := FilePath.mk "/proc" / e.fileName
    let comm ← match ← (IO.FS.readFile (base / "comm")).toBaseIO with
      | .ok s => pure s
      | .error _ => pure ""
    unless comm == "lean\n" do continue
    let cwd ← match ← (IO.FS.realPath (base / "cwd")).toBaseIO with
      | .ok p => pure p.toString
      | .error _ => pure ""
    unless cwd == root || cwd.startsWith (root ++ "/") do continue
    n := n + 1
    let argv ← match ← (IO.FS.readBinFile (base / "cmdline")).toBaseIO with
      | .ok b => pure b
      | .error _ => pure ByteArray.empty
    let mut args : Array String := #[]
    let mut s := 0
    for i in [0:argv.size] do
      if argv[i]! == 0 then
        args := args.push (lossyUtf8 (argv.extract s i))
        s := i + 1
    if let some src := (args.extract 1 args.size).find? (·.endsWith ".lean") then
      seen.modify fun m => m.insert src (match m[src]? with
        | some (a, _) => (a, now)
        | none => (now, now))
  peak.modify (max · n)

partial def samplerLoop (root : String) (t0 : Nat) (stop : IO.Ref Bool)
    (seen : IO.Ref (Std.HashMap String (Nat × Nat))) (peak : IO.Ref Nat) : IO Unit := do
  if ← stop.get then return
  try sampleLean root t0 seen peak catch _ => pure ()
  IO.sleep 500
  samplerLoop root t0 stop seen peak

structure BuildErr where
  file : String
  line : Nat
  col : Nat
  msg : String

structure BuildRes where
  rc : UInt32
  secs : Nat
  errors : Array BuildErr
  running : Array String
  peak : Nat
  /-- modules of `✖ … Building M` lines -/
  failedMods : Array String := #[]
  /-- of those, the ones whose `lean` could not create a thread (an address-space cap that is too
  small for the process's threads: an environment failure, not a failure of the rewrite) -/
  envFailed : Array String := #[]
  attempts : Nat := 1

/-- Path of `p` (absolute, or relative to `pkg`) relative to `pkg`, if it lies under it. -/
def relTo (pkg : FilePath) (p : String) : String :=
  let full := normPath (if (FilePath.mk p).isAbsolute then FilePath.mk p else pkg / p)
  match relComps? full (normPath pkg) with
  | some cs => joinSep "/" cs.toList
  | none => p

/-- `error: <file>.lean:<line>:<col>: <message>` -/
def parseErr? (pkg : FilePath) (l : String) : Option BuildErr := do
  guard (l.startsWith "error: ")
  let rest := String.ofList (l.toList.drop 7)
  match rest.splitOn ".lean:" with
  | p :: r :: rs =>
    match (".lean:".intercalate (r :: rs)).splitOn ":" with
    | ln :: cn :: msg =>
      let line ← ln.toNat?
      let col ← cn.toNat?
      let m := ":".intercalate msg
      some { file := relTo pkg (p ++ ".lean"), line, col,
             msg := String.ofList ((m.toList.dropWhile (· == ' ')).take 300) }
    | _ => none
  | _ => none

/-- `runCapped` with an optional address-space cap (`none`: no `ulimit -v`, like the plain
`lake build` of the main driver). -/
def runOpt (cmd : String) (args : Array String) (cwd : FilePath)
    (env : Array (String × Option String)) (timeout : Nat) (memGB : Option Nat) (log : FilePath) :
    IO (UInt32 × Nat) := do
  match memGB with
  | some g => runCapped cmd args cwd env { timeout, memGB := g } log
  | none =>
    let t0 ← IO.monoMsNow
    appendLine log s!"$ {cmd} {joinSep " " args.toList}"
    let script :=
      "L=$1; shift; " ++
      "ulimit -n 65536 2>/dev/null || ulimit -n \"$(ulimit -Hn)\" 2>/dev/null; " ++
      s!"timeout -k 30 {timeout} \"$@\" >>\"$L\" 2>&1 & c=$!; " ++
      "( n=0; while kill -0 \"$c\" 2>/dev/null; do " ++
      s!"if ! kill -0 \"$PPID\" 2>/dev/null || [ \"$n\" -ge {timeout + 120} ]; then " ++
      "kill -KILL -- \"-$c\" \"$c\" 2>/dev/null; break; fi; sleep 1; n=$((n+1)); done ) & " ++
      "wait \"$c\""
    let child ← IO.Process.spawn
      { cmd := "bash", args := #["-c", script, "ntrust-job", log.toString, cmd] ++ args,
        cwd := some cwd, env, setsid := true, stdin := .null, stdout := .null, stderr := .null }
    let rc ← child.wait
    let ms := (← IO.monoMsNow) - t0
    let rc := if rc == 137 && ms ≥ timeout * 1000 then 124 else rc
    appendLine log s!"rc={rc} secs={ms / 1000}"
    return (rc, ms)

/-- Modules of the `✖ [i/n] Building M` lines of a Lake log, and those among them whose process
reported `failed to create thread`. -/
def failedModules (txt : String) : Array String × Array String := Id.run do
  let mut failed := #[]
  let mut env := #[]
  let mut cur : Option String := none
  for l in textLines txt do
    if l.startsWith "✖" || l.startsWith "✔" || l.startsWith "⚠" || l.startsWith "ℹ" then
      cur := none
      if l.startsWith "✖" then
        match l.splitOn "Building " with
        | _ :: r :: _ =>
          let m := String.ofList (r.toList.takeWhile (· != ' '))
          failed := failed.push m
          cur := some m
        | _ => pure ()
    else if let some m := cur then
      if (l.splitOn "failed to create thread").length > 1 && !env.contains m then env := env.push m
  return (failed, env)

def lakeBuildOnce (lake : String) (pkg : FilePath) (targets : Array ModName) (log : FilePath)
    (jobs timeout : Nat) (mem : Option Nat) : IO BuildRes := do
  if ← log.pathExists then IO.FS.removeFile log
  let t0 ← IO.monoMsNow
  let stop ← IO.mkRef false
  let seen ← IO.mkRef ({} : Std.HashMap String (Nat × Nat))
  let peak ← IO.mkRef 0
  let root := (normPath pkg).toString
  let task ← IO.asTask (samplerLoop root t0 stop seen peak) .dedicated
  let (rc, ms) ← runOpt lake (#["build", "--no-ansi"] ++ targets.map ("+" ++ ·.esc)) pkg
    #[("LEAN_NUM_THREADS", some (toString jobs))] timeout mem log
  stop.set true
  discard <| IO.wait task
  let txt ← readText log
  let errors := (textLines txt).toArray.filterMap (parseErr? pkg)
  let mut running := #[]
  if rc == 124 then
    for (src, (_, last)) in (← seen.get).toList do
      if last + 5000 ≥ ms then running := running.push (relTo pkg src)
  let (failedMods, envFailed) := failedModules txt
  return { rc, secs := ms / 1000, errors, running, peak := ← peak.get, failedMods, envFailed }

/-- `lake build` of the targets; when the only failures are processes that could not create a
thread (environment), the build is repeated (Lake rebuilds just those) up to `retries` times. -/
def lakeBuild (lake : String) (pkg : FilePath) (targets : Array ModName) (log : FilePath)
    (jobs timeout : Nat) (mem : Option Nat) (retries : Nat := 3) : IO BuildRes := do
  let mut r ← lakeBuildOnce lake pkg targets log jobs timeout mem
  let mut secs := r.secs
  let mut peak := r.peak
  let mut k := 0
  while k < retries && r.rc != 0 && r.rc != 124 && r.errors.isEmpty && !r.envFailed.isEmpty &&
      r.failedMods.all r.envFailed.contains do
    k := k + 1
    let logK : FilePath := ⟨log.toString ++ s!".retry{k}"⟩
    r ← lakeBuildOnce lake pkg targets logK jobs timeout mem
    secs := secs + r.secs
    peak := max peak r.peak
  return { r with secs, peak, attempts := k + 1 }

/-! ## Rewriting -/

/-- Write every file from its original text with the active occurrences replaced; record the
new column spans (replacements never contain newlines, so lines stay). -/
def applyRewrites (pkg origDir : FilePath) (occs : Array Occ) (byFile : Array (String × Array Nat))
    (active : Std.HashSet Nat) : IO (Array Occ) := do
  let mut occs := occs
  for (rel, ids) in byFile do
    let src := (← readText (origDir / rel)).toList.toArray
    let mut out := ""
    let mut last := 0
    let mut delta : Std.HashMap Nat Int := {}
    for id in ids do
      let o := occs[id]!
      out := out ++ substr src last o.start ++ (if active.contains id then o.new else o.old)
      last := o.stop
      let d := delta.getD o.line 0
      let newCol := (Int.ofNat o.col + d).toNat
      let len := if active.contains id then o.new.length else o.old.length
      occs := occs.set! id { o with newCol, newEnd := newCol + len }
      if active.contains id then
        delta := delta.insert o.line (d + Int.ofNat o.new.length - Int.ofNat o.old.length)
    out := out ++ substr src last src.size
    let target := pkg / rel
    if (← readText target) != out then IO.FS.writeFile target out
  return occs

/-- Occurrences to revert for the build errors: same line and column span, else the active
occurrences on that line, else those in the enclosing declaration, else all of the file. -/
def attributeErrors (errors : Array BuildErr) (occs : Array Occ) (byFile : Std.HashMap String (Array Nat))
    (active : Std.HashSet Nat) (declRanges : Std.HashMap String (Array (Nat × Nat))) :
    Std.HashMap Nat String × Array BuildErr := Id.run do
  let mut hit : Std.HashMap Nat String := {}
  let mut unattributed := #[]
  for e in errors do
    let act := (byFile.getD e.file #[]).filter active.contains |>.map (occs[·]!)
    if act.isEmpty then
      unattributed := unattributed.push e
      continue
    let mut c := act.filter fun o => o.line == e.line && o.newCol ≤ e.col && e.col < o.newEnd
    if c.isEmpty then c := act.filter (·.line == e.line)
    if c.isEmpty then
      for (l1, l2) in declRanges.getD e.file #[] do
        if l1 ≤ e.line && e.line ≤ l2 then
          c := act.filter fun o => l1 ≤ o.line && o.line ≤ l2
          if !c.isEmpty then break
    if c.isEmpty then c := act
    for o in c do
      unless hit.contains o.id do hit := hit.insert o.id e.msg
  return (hit, unattributed)

/-! ## Main -/

def countMap (xs : Array String) : List (String × Nat) := Id.run do
  let mut m : Std.HashMap String Nat := {}
  for x in xs do m := m.insert x (m.getD x 0 + 1)
  return m.toList.toArray.qsort (fun a b => a.2 > b.2 || (a.2 == b.2 && a.1 < b.1)) |>.toList

def jsonObj (kvs : List (String × String)) : String :=
  "{" ++ joinSep ", " (kvs.map fun (k, v) => jsonStr k ++ ": " ++ v) ++ "}"

/-- Put back the originals that the last run saved (the files listed in `manifest`, copies in
`origDir`); returns how many. -/
def restoreOriginals (pkg origDir manifest : FilePath) : IO Nat := do
  if !(← manifest.pathExists) then return 0
  let mut n := 0
  for rel in textLines (← readText manifest) do
    if rel == "" then continue
    let src := origDir / rel
    if ← src.pathExists then
      IO.FS.writeBinFile (pkg / rel) (← IO.FS.readBinFile src)
      n := n + 1
  return n

def run (o : MOpts) : IO UInt32 := do
  let pkg ← IO.FS.realPath (← IO.currentDir)
  let outBase := normPath (if (FilePath.mk o.out).isAbsolute then o.out else pkg / o.out)
  let out := outBase / "migrate"
  let origDir := out / "orig"
  let manifest := out / "orig.files"
  let marker := out / "incomplete"
  IO.FS.createDirAll out
  let lake := (← IO.getEnv "LAKE").getD "lake"
  -- undo an interrupted run (or `--restore`)
  if o.restore || (← marker.pathExists) then
    let n ← restoreOriginals pkg origDir manifest
    IO.println s!"ntrust migrate: restored {n} original file(s) from {origDir} \
      ({if o.restore then "--restore" else "the last run was interrupted"})"
    if ← marker.pathExists then IO.FS.removeFile marker
    if o.restore then return 0
  let log (s : String) : IO Unit := do
    IO.println s!"ntrust migrate: {s}"
    appendLine (out / "migrate.log") s
  -- project files and modules
  let skip (p : FilePath) (n : String) : Bool :=
    n.startsWith "." || n == "lake-packages" || normPath p == outBase
  let files := (← walkLean pkg skip).filter fun f => f.fileName != some "lakefile.lean"
  let mut modOfFile : Std.HashMap String ModName := {}
  let mut fileOfMod : Std.HashMap String String := {}
  for f in files do
    if let some m ← moduleOf f (← pkgRootOf f pkg) then
      let rel := relTo pkg f.toString
      modOfFile := modOfFile.insert rel m
      unless fileOfMod.contains m.dotted do
        fileOfMod := fileOfMod.insert m.dotted rel
        fileOfMod := fileOfMod.insert m.esc rel
  let lp ← projectLeanPath lake pkg
  let lean ← findLean lake pkg
  let pkgN := (normPath pkg).toString
  let ownLp ← lp.filterM fun (d : String) => do
    let r ← match ← (IO.FS.realPath (FilePath.mk d)).toBaseIO with
      | .ok p => pure (normPath p).toString
      | .error _ => pure (normPath (FilePath.mk d)).toString
    return r == pkgN || r.startsWith (pkgN ++ "/")
  let mut built : Array ModName := #[]
  for (_, m) in modOfFile.toList do
    if (← findIn ownLp (m.relPath "olean")).isSome then built := built.push m
  built := built.qsort (fun a b => a.dotted < b.dotted)
  let tc := (← readText (pkg / "lean-toolchain")).replace "\n" ""
  log s!"{pkg}: toolchain {tc}, {files.size} files, {modOfFile.size} modules, {built.size} built"
  -- 1. census before
  let c0 ← runCensus lean lp (out / "census_before") built o.jobs o.batch o.mem
  log s!"census before: {c0.ax.size} native axioms, {c0.dirty.size} native-dependent declarations, \
    {c0.mods.size} modules, failed {c0.failed.toList}"
  -- 2. plan
  let mut occs : Array Occ := #[]
  for f in files do
    let rel := relTo pkg f.toString
    let found := occurrencesIn rel (← readText f)
    for x in found do
      occs := occs.push { x with id := occs.size, module := (modOfFile[rel]?.map (·.dotted)).getD "" }
  let mut byPos : Std.HashMap (String × Nat × Nat) Nat := {}
  for x in occs do byPos := byPos.insert (x.file, x.line, x.col) x.id
  let mut unmatched := 0
  for a in c0.ax do
    let some (l, c, _, _) := a.range | unmatched := unmatched + 1; continue
    let some rel := fileOfMod[a.module]? | unmatched := unmatched + 1; continue
    match byPos[(rel, l, c)]? with
    | some id => occs := occs.set! id { occs[id]! with facts := occs[id]!.facts.push a.axiomName }
    | none => unmatched := unmatched + 1
  let mut declRanges : Std.HashMap String (Array (Nat × Nat)) := {}
  for (m, pr) in c0.ax.map (fun a => (a.module, a.prange)) ++ c0.dirty.map (fun d => (d.module, d.prange)) do
    if let (some rel, some (l1, _, l2, _)) := (fileOfMod[m]?, pr) then
      let cur := declRanges.getD rel #[]
      unless cur.contains (l1, l2) do declRanges := declRanges.insert rel (cur.push (l1, l2))
  declRanges := declRanges.fold (init := {}) fun acc k v =>
    acc.insert k (v.qsort fun a b => a.2 - a.1 < b.2 - b.1)
  let report ← match o.report with
    | some p => some <$> loadReport (if (FilePath.mk p).isAbsolute then p else pkg / p)
    | none => pure none
  let builtSet : Std.HashSet String := built.foldl (fun s m => s.insert m.dotted) {}
  for i in [0:occs.size] do
    let x := occs[i]!
    let (st, why) : String × String :=
      if x.inMacro then ("keep", "inside a macro/syntax definition")
      else if !builtSet.contains x.module then ("keep", "module not built")
      else if x.facts.isEmpty then
        if o.noUnknown then ("keep", "no fact in the olean (example?)")
        else ("try", "no fact in the olean (example?): the build decides")
      else match report with
        | none => ("rewrite", "")
        | some rep => Id.run do
          let mut bad : Array String := #[]
          for ax in x.facts do
            match rep[ax]? with
            | some ("PROVED", _) => pure ()
            | some (v, r) => bad := bad.push s!"report {v}/{r}"
            | none => bad := bad.push "no per-fact result"
          if bad.isEmpty then return ("rewrite", "")
          return ("keep", bad[0]! ++ (if bad.size > 1 then s!" (+{bad.size - 1} more facts)" else ""))
    occs := occs.set! i { x with status := st, reason := why }
  let affected : Array String :=
    (occs.filter (fun x => x.status == "rewrite" || x.status == "try")).map (·.module)
      |>.foldl (fun s m => if s.contains m then s else s.push m) #[] |>.qsort (· < ·)
  let planCounts := countMap (occs.map fun x => x.status ++ (if x.status == "keep" then ": " ++ x.reason else ""))
  log s!"plan: {occs.size} occurrences; {planCounts}; unmatched axioms {unmatched}; \
    affected modules {affected.size}"
  let writePlan (occs : Array Occ) : IO Unit := do
    let lines := occs.toList.map fun x =>
      joinSep "\t" [x.file, toString x.line, toString x.col, x.form, x.status, tsvField x.reason,
        joinSep "," x.facts.toList]
    IO.FS.writeFile (out / "plan.tsv")
      (joinSep "\n" ("file\tline\tcol\tform\tstatus\treason\tfacts" :: lines) ++ "\n")
  writePlan occs
  if o.dryRun then return 0
  -- 3. originals, rewrite, build rounds
  let mut byFileM : Std.HashMap String (Array Nat) := {}
  for x in occs do byFileM := byFileM.insert x.file ((byFileM.getD x.file #[]).push x.id)
  let byFile := byFileM.toList.toArray
  for (rel, _) in byFile do
    let dst := origDir / rel
    if let some d := dst.parent then IO.FS.createDirAll d
    IO.FS.writeBinFile dst (← IO.FS.readBinFile (pkg / rel))
  IO.FS.writeFile manifest (joinSep "\n" (byFile.toList.map (·.1)) ++ "\n")
  IO.FS.writeFile marker "rewrite in progress; the next run restores the originals\n"
  let modName (s : String) : ModName := ((built.find? (·.dotted == s)).getD #[s])
  let buildMem : Option Nat := if o.buildMem == 0 then none else some o.buildMem
  let mut active : Std.HashSet Nat := {}
  for x in occs do
    if x.status == "rewrite" || x.status == "try" then active := active.insert x.id
  let mut reverted : Std.HashMap Nat String := {}
  let mut rounds : Array String := #[]
  let mut ok := false
  for rnd in [0:o.rounds] do
    occs ← applyRewrites pkg origDir occs byFile active
    let targets := (occs.filter (active.contains ·.id)).map (·.module)
      |>.foldl (fun s m => if s.contains m then s else s.push m) #[]
    if targets.isEmpty then
      ok := true
      break
    let b ← lakeBuild lake pkg (targets.map modName) (out / s!"build_round{rnd}.log") o.jobs
      o.roundTimeout buildMem
    let (hit0, unattr) := attributeErrors b.errors occs byFileM active declRanges
    let mut hit := hit0
    if b.rc == 124 then
      for rel in b.running do
        let act := (byFileM.getD rel #[]).filter active.contains
        let tried := act.filter (occs[·]!.status == "try")
        for id in (if tried.isEmpty then act else tried) do
          unless hit.contains id do
            hit := hit.insert id s!"build of the module exceeded {o.roundTimeout} s"
    -- modules that still could not create a thread after the retries: tried again in the next
    -- round (the failure depends on how many elaboration threads run at once); in the last round
    -- their occurrences are reverted, since they could not be verified here
    let lastRound := rnd + 1 == o.rounds
    if lastRound then
      for m in b.envFailed do
        for id in active.toList do
          if occs[id]!.module == m && !hit.contains id then
            hit := hit.insert id "module could not be built here (failed to create thread; raise --build-mem)"
    let envOnly := b.rc != 0 && b.rc != 124 && b.errors.isEmpty && !b.envFailed.isEmpty &&
      b.failedMods.all b.envFailed.contains
    if b.rc != 0 && hit.isEmpty && !envOnly then
      -- unattributable failure: revert the active occurrences of the modules that failed (of all
      -- target modules when none can be named)
      let failed := b.failedMods.filter targets.contains
      for id in active.toList do
        let m := occs[id]!.module
        if (if failed.isEmpty then targets.contains m else failed.contains m) then
          hit := hit.insert id "unattributed build failure"
    rounds := rounds.push (jsonObj [("round", toString rnd), ("rc", toString b.rc),
      ("secs", toString b.secs), ("attempts", toString b.attempts),
      ("errors", toString b.errors.size), ("reverted", toString hit.size),
      ("unattributed", toString unattr.size), ("env_failed", toString b.envFailed.size),
      ("peak_lean", toString b.peak)])
    log s!"build round {rnd}: rc={b.rc} {b.secs}s attempts={b.attempts} errors={b.errors.size} \
      revert={hit.size} unattributed={unattr.size} env_failed={b.envFailed.size} peak_lean={b.peak}"
    if b.rc == 0 then
      ok := true
      break
    for (id, msg) in hit.toList do
      active := active.erase id
      reverted := reverted.insert id msg
  if !ok then
    occs ← applyRewrites pkg origDir occs byFile active
  for i in [0:occs.size] do
    let x := occs[i]!
    if let some msg := reverted[i]? then
      occs := occs.set! i { x with status := "keep", reason := "build: " ++ msg }
    else if active.contains i then
      occs := occs.set! i { x with status := "replaced" }
  -- 4. verification
  let mut finalRc : UInt32 := if ok then 0 else 1
  let mut finalErrs : Array BuildErr := #[]
  let mut finalEnv : Array String := #[]
  if ok && !o.skipFinal then
    let b ← lakeBuild lake pkg built (out / "build_final.log") o.jobs o.buildTimeout buildMem
      (retries := 6)
    finalRc := b.rc
    finalErrs := b.errors
    finalEnv := b.envFailed
    log s!"final build of {built.size} modules: rc={b.rc} {b.secs}s attempts={b.attempts} \
      errors={b.errors.size} env_failed={b.envFailed.toList}"
  if ← marker.pathExists then IO.FS.removeFile marker
  let c1 ← runCensus lean lp (out / "census_after") built o.jobs o.batch o.mem
  let dirty1 : Std.HashSet String := c1.dirty.foldl (fun s d => s.insert d.decl) {}
  let parentOfAx : Std.HashMap String String := c0.ax.foldl (fun m a => m.insert a.axiomName a.parent) {}
  let mut rewritten : Std.HashSet String := {}
  for x in occs do
    if x.status == "replaced" then
      for f in x.facts do
        if let some p := parentOfAx[f]? then rewritten := rewritten.insert p
  let still := rewritten.toList.filter dirty1.contains
  let why := still.map fun d =>
    let own := (c1.ax.filter (·.parent == d)).size
    (d, if own > 0 then s!"{own} unconverted native facts of its own"
        else "depends on another native-dependent declaration")
  let replaced := occs.filter (·.status == "replaced")
  let remaining := countMap ((occs.filter (·.status != "replaced")).map (·.reason))
  let summary := jsonObj [
    ("project", jsonStr pkg.toString), ("toolchain", jsonStr tc),
    ("uses", toString occs.size), ("replaced", toString replaced.size),
    ("replaced_known", toString (replaced.filter (!·.facts.isEmpty)).size),
    ("replaced_unknown", toString (replaced.filter (·.facts.isEmpty)).size),
    ("remaining", jsonObj (remaining.map fun (r, n) => (r, toString n))),
    ("native_axioms_before", toString c0.ax.size), ("native_axioms_after", toString c1.ax.size),
    ("bv_decide_axioms_after", toString (c1.ax.filter (·.tactic == "bv_decide")).size),
    ("native_dependent_decls_before", toString c0.dirty.size),
    ("native_dependent_decls_after", toString c1.dirty.size),
    ("rewritten_decls", toString rewritten.size),
    ("rewritten_decls_still_native", toString still.length),
    ("still_native_why", jsonObj (why.map fun (d, w) => (d, jsonStr w))),
    ("build_ok", if ok && finalRc == 0 then "true" else "false"),
    ("rounds", jsonArr rounds.toList),
    ("final_build", jsonObj [("rc", toString finalRc),
      ("env_failed", jsonArr (finalEnv.toList.map jsonStr)),
      ("errors", jsonArr (finalErrs.toList.take 20 |>.map fun e =>
        jsonStr s!"{e.file}:{e.line}:{e.col}: {e.msg}"))]),
    ("census_failed", jsonObj [("before", jsonArr (c0.failed.toList.map jsonStr)),
      ("after", jsonArr (c1.failed.toList.map jsonStr))]),
    ("affected_modules", toString affected.size),
    ("unmatched_axioms", toString unmatched)]
  IO.FS.writeFile (out / "summary.json") (summary ++ "\n")
  writePlan occs
  -- patch: original vs rewritten, files with a replacement
  let mut patch := ""
  let pfiles : Array String :=
    (replaced.map (·.file)).foldl (fun (s : Array String) f => if s.contains f then s else s.push f) #[]
  for rel in pfiles.qsort (fun a b => a < b) do
    let r ← IO.Process.output { cmd := "diff", args := #["-u", "--label", s!"a/{rel}", "--label",
      s!"b/{rel}", (origDir / rel).toString, (pkg / rel).toString] }
    patch := patch ++ r.stdout
  IO.FS.writeFile (out / "migrate.patch") patch
  log s!"{occs.size} uses, {replaced.size} replaced ({(replaced.filter (!·.facts.isEmpty)).size} with \
    facts, {(replaced.filter (·.facts.isEmpty)).size} examples); native axioms {c0.ax.size} → \
    {c1.ax.size}; native-dependent declarations {c0.dirty.size} → {c1.dirty.size}; rewritten \
    declarations still native {still.length} of {rewritten.size}; build {if ok && finalRc == 0 then "OK" else "FAILED"}"
  log s!"outputs: {out / "summary.json"}, {out / "plan.tsv"}, {out / "migrate.patch"}"
  return (if ok && finalRc == 0 then 0 else 1 : UInt32)

def main (args : List String) : IO UInt32 := do
  match parseArgs args {} with
  | .error e =>
    IO.eprintln s!"ntrust migrate: {e}\n\n{usage}"
    return 2
  | .ok o =>
    if o.help then
      IO.println usage
      return 0
    try run o catch e =>
      IO.eprintln s!"ntrust migrate: error: {e}"
      return (2 : UInt32)

end NativeTrust.Driver.Migrate
