import Std.Data.HashMap
import Std.Data.HashSet
import Std.Sync.Mutex

/-!
# `ntrust` helpers: byte search, processes under limits, a job pool

The driver imports only `Init` and `Std` (no `Lean`, no `NativeTrust` library modules): it never
elaborates Lean code itself, it generates small Lean files and runs `lean` on them.
-/

namespace NativeTrust.Driver

open System

/-! ## Bytes and text -/

/-- The ASCII/UTF-8 string `s` occurs in `b` at byte offset `i`. -/
def bytesHasAt (b : ByteArray) (i : Nat) (s : String) : Bool := Id.run do
  let sb := s.toUTF8
  if i + sb.size > b.size then return false
  for j in [0:sb.size] do
    if b[i + j]! != sb[j]! then return false
  return true

/-- First offset `≥ start` at which `s` occurs in `b`. -/
def bytesFind? (b : ByteArray) (s : String) (start : Nat := 0) : Option Nat := Id.run do
  let sb := s.toUTF8
  if sb.size == 0 then return some start
  if b.size < sb.size then return none
  let c0 := sb[0]!
  for i in [start:b.size - sb.size + 1] do
    if b[i]! == c0 && bytesHasAt b i s then return some i
  return none

def bytesContains (b : ByteArray) (s : String) : Bool := (bytesFind? b s).isSome

def isWsByte (c : UInt8) : Bool := c == 32 || c == 9 || c == 10 || c == 13 || c == 12 || c == 11

def isWordByte (c : UInt8) : Bool :=
  (c ≥ 48 && c ≤ 57) || (c ≥ 65 && c ≤ 90) || (c ≥ 97 && c ≤ 122) || c == 95

def skipWs (b : ByteArray) (i : Nat) : Nat := Id.run do
  let mut j := i
  while j < b.size && isWsByte b[j]! do j := j + 1
  return j

/-- `s` occurs in `b` at a word boundary on its left (regex `\bs`). -/
def bytesContainsWord (b : ByteArray) (s : String) : Bool := Id.run do
  let mut from_ := 0
  repeat
    match bytesFind? b s from_ with
    | none => return false
    | some i =>
      if i == 0 || !isWordByte b[i - 1]! then return true
      from_ := i + 1
  return false

/-- UTF-8 decoding that never fails (invalid input: one character per byte). -/
def lossyUtf8 (b : ByteArray) : String :=
  match String.fromUTF8? b with
  | some s => s
  | none => String.ofList (b.toList.map fun c => Char.ofNat c.toNat)

def readText (p : FilePath) : IO String := do
  if ← p.pathExists then return lossyUtf8 (← IO.FS.readBinFile p) else return ""

/-- The decimal number right after the first occurrence of `key` (regex `key(\d+)`). -/
def bytesNatAfter? (b : ByteArray) (key : String) : Option Nat := Id.run do
  let mut from_ := 0
  repeat
    match bytesFind? b key from_ with
    | none => return none
    | some i =>
      let mut j := i + key.utf8ByteSize
      let mut n := 0
      let mut any := false
      while j < b.size && b[j]! ≥ 48 && b[j]! ≤ 57 do
        n := n * 10 + (b[j]! - 48).toNat
        j := j + 1
        any := true
      if any then return some n
      from_ := i + 1
  return none

/-- All texts `x` (non-empty, without backquote) in occurrences of `pre ++ x ++ "`"`. -/
def bytesCaptures (b : ByteArray) (pre : String) : Array String := Id.run do
  let mut out := #[]
  let mut from_ := 0
  repeat
    match bytesFind? b pre from_ with
    | none => break
    | some i =>
      let s := i + pre.utf8ByteSize
      let mut j := s
      while j < b.size && b[j]! != 96 do j := j + 1
      if j < b.size && j > s then
        out := out.push (lossyUtf8 (b.extract s j))
      from_ := i + 1
  return out

/-- Lines of a text. -/
def textLines (s : String) : List String := s.splitOn "\n"

/-- The tag of an output line `TAG\t…`, also when Lean prefixed the first line of a message with
`file:line:col: info: `. -/
def lineFields (l : String) : String × List String :=
  match l.splitOn "\t" with
  | [] => ("", [])
  | c :: cs => ((c.splitOn " ").getLast!, cs)

def sanitize (s : String) : String :=
  String.ofList (s.toList.map fun c => if c.isAlphanum || c == '_' then c else '_')

def joinSep (sep : String) (xs : List String) : String := sep.intercalate xs

/-- A TSV field: tabs and newlines become spaces. -/
def tsvField (s : String) : String :=
  String.ofList (s.toList.map fun c => if c == '\t' || c == '\n' || c == '\r' then ' ' else c)

def hex4 (n : Nat) : String :=
  let d := Nat.toDigits 16 n
  String.ofList (List.replicate (4 - d.length) '0' ++ d)

/-- A JSON string literal. -/
def jsonStr (s : String) : String := Id.run do
  let mut out := "\""
  for c in s.toList do
    out := match c with
      | '"' => out ++ "\\\""
      | '\\' => out ++ "\\\\"
      | '\n' => out ++ "\\n"
      | '\r' => out ++ "\\r"
      | '\t' => out ++ "\\t"
      | c => if c.toNat < 32 then out ++ "\\u" ++ hex4 c.toNat else out.push c
  return out.push '"'

def jsonArr (xs : List String) : String := "[" ++ joinSep ", " xs ++ "]"

/-! ## Processes -/

/-- Limits of one `lean` process. -/
structure Limits where
  /-- Seconds, enforced by coreutils `timeout -k 30` on the process group. -/
  timeout : Nat
  /-- Address-space cap (`ulimit -v`) in GB. -/
  memGB : Nat

/-- Append a line to a file (created if needed). -/
def appendLine (p : FilePath) (line : String) : IO Unit :=
  IO.FS.withFile p .append fun h => h.putStrLn line

/-- Run `cmd args` in `cwd` with environment changes `env` under `lim`, standard output and error
appended to `log`. Returns the exit code (`124` on timeout) and the wall time in ms.

The job runs as `bash -c`, in its own session: `ulimit -v`, then `timeout -k 30 S cmd args`
(which kills the job's whole process group at the limit). A watchdog kills that group when the
driver process disappears (so an interrupted driver leaves no `lean` behind) or when the limit plus
two minutes has passed (backstop). -/
def runCapped (cmd : String) (args : Array String) (cwd : FilePath)
    (env : Array (String × Option String)) (lim : Limits) (log : FilePath) : IO (UInt32 × Nat) := do
  let t0 ← IO.monoMsNow
  appendLine log s!"$ {cmd} {joinSep " " args.toList}"
  let script :=
    "L=$1; shift; " ++
    "ulimit -n 65536 2>/dev/null || ulimit -n \"$(ulimit -Hn)\" 2>/dev/null; " ++
    s!"ulimit -v {lim.memGB * 1024 * 1024} 2>/dev/null; " ++
    s!"timeout -k 30 {lim.timeout} \"$@\" >>\"$L\" 2>&1 & c=$!; " ++
    "( n=0; while kill -0 \"$c\" 2>/dev/null; do " ++
    s!"if ! kill -0 \"$PPID\" 2>/dev/null || [ \"$n\" -ge {lim.timeout + 120} ]; then " ++
    "kill -KILL -- \"-$c\" \"$c\" 2>/dev/null; break; fi; sleep 1; n=$((n+1)); done ) & " ++
    "wait \"$c\""
  let child ← IO.Process.spawn
    { cmd := "bash", args := #["-c", script, "ntrust-job", log.toString, cmd] ++ args,
      cwd := some cwd, env, setsid := true, stdin := .null, stdout := .null, stderr := .null }
  let rc ← child.wait
  let ms := (← IO.monoMsNow) - t0
  let rc := if rc == 137 && ms ≥ lim.timeout * 1000 then 124 else rc
  appendLine log s!"rc={rc} secs={ms / 1000}"
  return (rc, ms)

/-- Run `cmd args` in `cwd` (no limits), standard output and error appended to `log`. -/
def runLogged (cmd : String) (args : Array String) (cwd : FilePath)
    (env : Array (String × Option String)) (log : FilePath) : IO UInt32 := do
  appendLine log s!"$ {cmd} {joinSep " " args.toList}"
  let child ← IO.Process.spawn
    { cmd := "bash", args := #["-c", "L=$1; shift; \"$@\" >>\"$L\" 2>&1", "ntrust-run",
        log.toString, cmd] ++ args,
      cwd := some cwd, env, stdin := .null, stdout := .null, stderr := .null }
  let rc ← child.wait
  appendLine log s!"rc={rc}"
  return rc

/-- Standard output of `cmd args` in `cwd`, if it exits with code 0. -/
def captureOutput? (cmd : String) (args : Array String) (cwd : FilePath) : IO (Option String) := do
  try
    let o ← IO.Process.output { cmd, args, cwd := some cwd }
    return if o.exitCode == 0 then some o.stdout else none
  catch _ => return none

/-! ## Job pool -/

/-- `f` on every element of `xs`, at most `jobs` at a time (one dedicated thread per worker; the
workers take the next index from a shared counter). Results in the order of `xs`. -/
def parMap {α β : Type} (jobs : Nat) (xs : Array α) (f : α → IO β) : IO (Array β) := do
  if xs.isEmpty then return #[]
  let next ← IO.mkRef 0
  let res ← IO.mkRef (Array.replicate xs.size (none : Option β))
  let worker : IO Unit := do
    repeat
      let i ← next.modifyGet fun i => (i, i + 1)
      if h : i < xs.size then
        let r ← f xs[i]
        res.modify fun a => a.set! i (some r)
      else
        break
  let mut tasks := #[]
  for _ in [0:max 1 (min jobs xs.size)] do
    tasks := tasks.push (← IO.asTask worker .dedicated)
  for t in tasks do
    match ← IO.wait t with
    | .ok _ => pure ()
    | .error e => throw e
  let out ← res.get
  out.mapM fun
    | some r => pure r
    | none => throw (IO.userError "ntrust: a job produced no result")

/-- A log file that several threads append lines to. -/
structure SharedLog where
  path : FilePath
  lock : Std.Mutex Unit

def SharedLog.new (path : FilePath) : IO SharedLog :=
  return { path, lock := ← Std.Mutex.new () }

def SharedLog.line (l : SharedLog) (s : String) : IO Unit :=
  l.lock.atomically (m := IO) do appendLine l.path s

end NativeTrust.Driver
