module

public import LeanAgent.Util
public import LeanAgent.Files
public import LeanAgent.Verify
public meta import LeanAgent.Util

/-!
Builder tools: the Lean toolchain, `lake build`, `lake test` and the kernel
re-checker (`leanchecker`, `leanchecker-paranoid`) run on a real project. Like
`Verify`, each run is an *observation*: it may write build artifacts under the
project's `.lake`, but never sources, git or a store.

A run is confined to a project directory inside the sandbox root (the same
path rule as `Files`), target and module names are checked so they cannot pass
a flag, and every run is bounded by a timeout. The result is a `Verdict` with
the compiler's diagnostics parsed into file, line and column, never an exception.

What the confinement does not do: `lake` runs the project's lakefile, which is a
Lean program, and `lean` elaborates project code, which can run `IO`. The
sandbox root bounds the paths these tools are pointed at, not what the project
does once it runs. A hostile project needs an OS sandbox around the process.
-/

namespace LeanAgent.Build

open LeanAgent

public section

/-- One compiler message: `file:line:column`, severity, text. -/
public structure Diagnostic where
  file : String
  line : Nat
  column : Nat
  severity : String
  message : String
  deriving Repr, BEq

public def Diagnostic.render (d : Diagnostic) : String :=
  s!"{d.file}:{d.line}:{d.column}: {d.severity}: {d.message}"

private def severities : List String := ["error", "warning", "info"]

private def dropChars (s : String) (n : Nat) : String := String.ofList (s.toList.drop n)

/-- `file.lean:line:column: text`, if `s` has that shape. -/
private def located (s : String) : Option (String × Nat × Nat × String) :=
  match s.splitOn ":" with
  | file :: line :: column :: rest =>
    if !file.endsWith ".lean" then none else do
    let l ← line.toNat?
    let c ← column.toNat?
    pure (file, l, c, (":".intercalate rest).trimAscii.copy)
  | _ => none

/-- A diagnostic line in `lake`'s spelling (`error: f.lean:4:15: text`) or
`lean`'s (`f.lean:4:15: error: text`). Anything else, such as lake's
`error: build failed` summary, is not a diagnostic. -/
public def parseLine (line : String) : Option Diagnostic :=
  let t := line.trimAscii.copy
  match severities.find? (fun sev => t.startsWith (sev ++ ": ")) with
  | some sev => do
    let (file, l, c, message) ← located (dropChars t (sev.length + 2))
    pure { file, line := l, column := c, severity := sev, message }
  | none => do
    let (file, l, c, rest) ← located t
    let sev ← severities.find? (fun sev => rest.startsWith (sev ++ ": "))
    pure { file, line := l, column := c, severity := sev, message := dropChars rest (sev.length + 2) }

public def parseDiagnostics (output : String) : Array Diagnostic :=
  ((output.splitOn "\n").filterMap parseLine).toArray

/-- A lake target or module name: non-blank, not a flag, and only name
characters (letters, digits, `.`, `_`, `-`, `'`, and `«»` quoting). -/
public def safeName (s : String) : Bool :=
  nonemptyText s && !s.startsWith "-" &&
    s.toList.all (fun c => c.isAlphanum || "._-'«»".toList.contains c)

/-- Where builder tools may run, and how long each run may take. -/
public structure Sandbox where
  root : System.FilePath
  timeoutSecs : Nat := 600

/-- The outcome of one build, test or kernel check. -/
public structure Verdict where
  ok : Bool
  command : String
  exitCode : UInt32 := 0
  timedOut : Bool := false
  diagnostics : Array Diagnostic := #[]
  /-- The end of the combined output, where lake reports what failed. -/
  output : String := ""
  deriving Repr

/-- The last `n` characters: a failing build reports at the end. -/
public def clipTail (s : String) (n : Nat := 4000) : String :=
  if s.length ≤ n then s else String.ofList (s.toList.drop (s.length - n))

public def Verdict.render (v : Verdict) : String :=
  let head := if v.ok then s!"OK: {v.command}"
    else if v.timedOut then s!"FAIL: {v.command} (timed out)"
    else s!"FAIL: {v.command} (exit {v.exitCode})"
  let diags := v.diagnostics.toList.map Diagnostic.render
  "\n".intercalate (head :: diags ++ (if v.ok || v.output.isEmpty then [] else ["--- output ---", v.output]))

private def refused (command reason : String) : Verdict :=
  { ok := false, command, exitCode := 1, output := reason }

/-- The project directory, if `project` names one inside the sandbox (`.` is
the root). Lexical; `projectDirIO` also follows symlinks. -/
public def projectDir (sb : Sandbox) (project : String) : Option System.FilePath :=
  if project == "." then some sb.root else Files.resolve sb.root project

/-- `projectDir`, with the real path (symlinks followed) confined to the root. -/
public def projectDirIO (sb : Sandbox) (project : String) : IO (Option System.FilePath) :=
  if project == "." then pure (some sb.root) else Files.confine sb.root project

private def runIn (sb : Sandbox) (project : String) (args : Array String) : IO Verdict := do
  let command := " ".intercalate ("lake" :: args.toList)
  let some dir ← projectDirIO sb project
    | return refused command s!"project `{project}` is outside the sandbox"
  unless ← (dir / "lakefile.lean").pathExists <||> (dir / "lakefile.toml").pathExists do
    return refused command s!"project `{project}` has no lakefile"
  try
    let (out, timedOut) ← Verify.runBounded { cmd := "lake", args, cwd := some dir } sb.timeoutSecs
    let all := out.stdout ++ "\n" ++ out.stderr
    pure { ok := out.exitCode == 0 && !timedOut, command, exitCode := out.exitCode, timedOut
           diagnostics := parseDiagnostics all, output := clipTail all.trimAscii.copy }
  catch e => pure (refused command s!"could not run lake: {e}")

/-- The toolchain a project pins (`lean-toolchain`) and the `lean` it actually gets. -/
public def toolchain (sb : Sandbox) (project : String) : IO String := do
  let some dir ← projectDirIO sb project
    | return s!"toolchain: project `{project}` is outside the sandbox"
  let pinned ← try IO.FS.readFile (dir / "lean-toolchain") catch _ => pure "(no lean-toolchain)"
  let v ← runIn sb project #["env", "lean", "--version"]
  pure s!"pinned: {pinned.trimAscii.copy}\nactive: {if v.ok then v.output else v.render}"

/-- `lake build` (the default targets when `target` is `default`). -/
public def lakeBuild (sb : Sandbox) (project target : String) : IO Verdict :=
  if target == "default" then runIn sb project #["build"]
  else if safeName target then runIn sb project #["build", target]
  else pure (refused s!"lake build {target}" s!"`{target}` is not a target name")

/-- `lake test`: the project's test driver. -/
public def lakeTest (sb : Sandbox) (project : String) : IO Verdict :=
  runIn sb project #["test"]

/-- Re-check a built module's declarations with the kernel, outside the
elaborator: `leanchecker`, or `leanchecker-paranoid` for the stricter check. -/
public def kernelCheck (sb : Sandbox) (project module : String) (paranoid : Bool) : IO Verdict :=
  let checker := if paranoid then "leanchecker-paranoid" else "leanchecker"
  if safeName module then runIn sb project #["env", checker, module]
  else pure (refused s!"{checker} {module}" s!"`{module}` is not a module name")

#guard (parseLine "error: Bad.lean:4:15: Type mismatch").map (·.line) == some 4
#guard (parseLine "A.lean:1:2: warning: unused").map (·.severity) == some "warning"
#guard (parseLine "error: build failed").isNone
#guard (parseLine "✔ [3/4] Built BuildOk (218ms)").isNone
#guard safeName "BuildOk.Basic" && !safeName "--help" && !safeName "a b"
#guard clipTail "abcdef" 2 == "ef"

end

end LeanAgent.Build
