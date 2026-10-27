import NativeTrust.Driver.Util

/-!
# `ntrust`: the user's Lake project

Source files that mention native evaluation, their module names (library `srcDir`s, nested
packages, components that are not identifiers written as `«…»`), the project's `LEAN_PATH` as
Lake computes it, and the build of the modules that have no `.olean` yet. Same logic as the
Python driver `ops/m2_axioms4.py` used for the 52,821-fact study.
-/

namespace NativeTrust.Driver

open System

/-- A module name as its components (`A.«b-c».D` is `#["A", "b-c", "D"]`). -/
abbrev ModName := Array String

def ModName.dotted (m : ModName) : String := joinSep "." m.toList

/-- Plain identifier component: `[A-Za-z_][A-Za-z0-9_'!?]*`. -/
def isPlainIdent (c : String) : Bool :=
  match c.toList with
  | [] => false
  | h :: t => (h.isAlpha || h == '_') &&
      t.all fun x => x.isAlphanum || x == '_' || x == '\'' || x == '!' || x == '?'

def escComp (c : String) : String := if isPlainIdent c then c else "«" ++ c ++ "»"

/-- The module name in Lean/Lake syntax. -/
def ModName.esc (m : ModName) : String := joinSep "." (m.toList.map escComp)

/-- The module's file relative to a source root, with extension `ext`. -/
def ModName.relPath (m : ModName) (ext : String) : FilePath :=
  ⟨joinSep "/" m.toList ++ "." ++ ext⟩

/-- A Lean term for the module's `Name` (no escaping issues). -/
def ModName.nameTerm (m : ModName) : String :=
  m.foldl (fun acc c => s!"(Lean.Name.mkStr {acc} {c.quote})") "Lean.Name.anonymous"

/-- Lexical normal form of an absolute path: no empty or `.` components, `..` resolved. -/
def normPath (p : FilePath) : FilePath := Id.run do
  let mut out : Array String := #[]
  for c in p.toString.splitOn "/" do
    if c == "" || c == "." then continue
    if c == ".." then out := out.pop else out := out.push c
  return ⟨"/" ++ joinSep "/" out.toList⟩

/-- Components of `p` relative to `root` (both normalized), if `p` lies strictly under `root`. -/
def relComps? (p root : FilePath) : Option (Array String) :=
  let ps := (p.toString.splitOn "/").filter (· != "")
  let rs := (root.toString.splitOn "/").filter (· != "")
  if rs.length < ps.length && ps.take rs.length == rs then some (ps.drop rs.length).toArray
  else none

/-- `srcDir` values in a lakefile (regex `srcDir\s*(?::=|=)\s*"([^"]+)"`). -/
def srcDirValues (b : ByteArray) : Array String := Id.run do
  let mut out := #[]
  let mut from_ := 0
  repeat
    match bytesFind? b "srcDir" from_ with
    | none => break
    | some i =>
      from_ := i + 1
      let j := skipWs b (i + 6)
      let j? := if bytesHasAt b j ":=" then some (j + 2)
        else if bytesHasAt b j "=" then some (j + 1) else none
      if let some j := j? then
        let k := skipWs b j
        if k < b.size && b[k]! == 34 then
          let mut e := k + 1
          while e < b.size && b[e]! != 34 do e := e + 1
          if e < b.size && e > k + 1 then out := out.push (lossyUtf8 (b.extract (k + 1) e))
  return out

/-- All `srcDir`s of the libraries of the package at `root` (each library may set its own),
except the package root itself. -/
def srcDirs (root : FilePath) : IO (Array FilePath) := do
  let mut out := #[]
  for lf in ["lakefile.toml", "lakefile.lean"] do
    let p := root / lf
    if ← p.pathExists then
      for v in srcDirValues (← IO.FS.readBinFile p) do
        let d := normPath (root / v)
        if d != normPath root then out := out.push d
  return out

/-- `.lean` files under `dir` (sorted, directory symlinks not followed), skipping the
directories for which `skipDir path name` holds. -/
partial def walkLean (dir : FilePath) (skipDir : FilePath → String → Bool) :
    IO (Array FilePath) := do
  let mut acc := #[]
  let entries ← match ← dir.readDir.toBaseIO with
    | .ok es => pure es
    | .error _ => pure #[]
  for e in entries.qsort (fun a b => a.fileName < b.fileName) do
    let p := e.path
    match ← p.symlinkMetadata.toBaseIO with
    | .ok { type := .dir, .. } =>
      unless skipDir p e.fileName do acc := acc ++ (← walkLean p skipDir)
    | .ok { type := .file, .. } =>
      if e.fileName.endsWith ".lean" then acc := acc.push p
    | .ok { type := .symlink, .. } =>
      if e.fileName.endsWith ".lean" then
        if (← p.metadata.toBaseIO) matches .ok { type := .file, .. } then acc := acc.push p
    | _ => pure ()
  return acc

/-- The regex of the Python driver,
`native_decide|decide\s*\+native|native\s*:=\s*true|bv_decide|ofReduceBool|ofReduceNat`. -/
def mentionsNative (b : ByteArray) : Bool := Id.run do
  for i in [0:b.size] do
    let c := b[i]!
    if c == 'n'.toUInt8 then
      if bytesHasAt b i "native_decide" then return true
      if bytesHasAt b i "native" then
        let j := skipWs b (i + 6)
        if bytesHasAt b j ":=" && bytesHasAt b (skipWs b (j + 2)) "true" then return true
    else if c == 'b'.toUInt8 then
      if bytesHasAt b i "bv_decide" then return true
    else if c == 'o'.toUInt8 then
      if bytesHasAt b i "ofReduceBool" || bytesHasAt b i "ofReduceNat" then return true
    else if c == 'd'.toUInt8 then
      if bytesHasAt b i "decide" && bytesHasAt b (skipWs b (i + 6)) "+native" then return true
  return false

/-- The project's `.lean` files that mention native evaluation, outside `lake-packages`, the
output directory and hidden directories (`.lake`, `.git`, the default output `.ntrust`). -/
def nativeFiles (pkg out : FilePath) : IO (Array FilePath) := do
  let outN := normPath out
  let skip (p : FilePath) (n : String) : Bool :=
    n.startsWith "." || n == "lake-packages" || normPath p == outN
  let mut res := #[]
  for f in ← walkLean pkg skip do
    match ← (IO.FS.readBinFile f).toBaseIO with
    | .ok b => if mentionsNative b then res := res.push f
    | .error _ => pure ()
  return res

/-- The nearest enclosing Lake package of file `f` (nested packages such as `ext/foo/` have
their own lakefile, and module names relative to their own source roots). -/
def pkgRootOf (f pkg : FilePath) : IO FilePath := do
  let pkgN := normPath pkg
  let mut d := normPath (f.parent.getD pkg)
  repeat
    if d == pkgN || (relComps? d pkgN).isNone then break
    if (← (d / "lakefile.toml").pathExists) || (← (d / "lakefile.lean").pathExists) then
      return d
    match d.parent with
    | some p => d := normPath p
    | none => break
  return pkg

/-- Module name of file `f`: relative to the library source root of its package that it lies
under (a library's `srcDir`), else relative to the package root. -/
def moduleOf (f root : FilePath) : IO (Option ModName) := do
  let stripExt (cs : Array String) : Array String :=
    match cs.back? with
    | some last => cs.pop.push (String.ofList (last.toList.take (last.length - ".lean".length)))
    | none => cs
  let fN := normPath f
  for r in ← srcDirs root do
    if let some cs := relComps? fN r then return some (stripExt cs)
  return (relComps? fN (normPath root)).map stripExt

/-- The project's search path as Lake computes it (`lake env printenv LEAN_PATH`: path
dependencies included); falls back to its `.lake/build` and `.lake/packages/*`. -/
def projectLeanPath (lake : String) (pkg : FilePath) : IO (Array String) := do
  if let some out ← captureOutput? lake #["env", "printenv", "LEAN_PATH"] pkg then
    let parts := ((out.replace "\n" "").splitOn ":").filter (· != "")
    unless parts.isEmpty do return parts.toArray
  let mut parts := #[(pkg / ".lake" / "build" / "lib" / "lean").toString]
  let pkgsDir := pkg / ".lake" / "packages"
  if ← pkgsDir.isDir then
    for e in (← pkgsDir.readDir).qsort (fun a b => a.fileName < b.fileName) do
      let d := e.path / ".lake" / "build" / "lib" / "lean"
      if ← d.isDir then parts := parts.push d.toString
  return parts

/-- The `lean` of the project's toolchain. -/
def findLean (lake : String) (pkg : FilePath) : IO String := do
  if let some out ← captureOutput? lake #["env", "printenv", "LEAN"] pkg then
    let l := out.replace "\n" ""
    if l != "" then
      if ← (FilePath.mk l).pathExists then return l
  if let some l ← IO.getEnv "LEAN" then
    if ← (FilePath.mk l).pathExists then return l
  return "lean"

/-- A directory of `path` that contains `rel`. -/
def findIn (path : Array String) (rel : FilePath) : IO (Option String) := do
  for d in path do
    if ← (FilePath.mk d / rel).pathExists then return some d
  return none

def hasOlean (path : Array String) (m : ModName) : IO Bool :=
  return (← findIn path (m.relPath "olean")).isSome

/-- `lake build` the modules (after `lake exe cache get` when the project depends on Mathlib);
then once more one by one for those still without an `.olean`. -/
def buildModules (lake : String) (pkg : FilePath) (lp : Array String) (mods : Array ModName)
    (logDir : FilePath) : IO Unit := do
  let manifest := pkg / "lake-manifest.json"
  if ← manifest.pathExists then
    let t := (lossyUtf8 (← IO.FS.readBinFile manifest)).map Char.toLower
    if (t.splitOn "mathlib").length > 1 then
      IO.println s!"ntrust: lake exe cache get (log {logDir / "cache.log"})"
      discard <| runLogged lake #["exe", "cache", "get"] pkg #[] (logDir / "cache.log")
  IO.println s!"ntrust: lake build of {mods.size} module(s) (log {logDir / "build.log"})"
  discard <| runLogged lake (#["build"] ++ mods.map (·.esc)) pkg #[] (logDir / "build.log")
  for m in mods do
    unless ← hasOlean lp m do
      discard <| runLogged lake #["build", m.esc] pkg #[] (logDir / "build_single.log")

end NativeTrust.Driver
