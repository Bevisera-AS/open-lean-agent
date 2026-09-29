module

public import LeanAgent.Util
public meta import LeanAgent.Util

namespace LeanAgent.Files

open LeanAgent

public section

/-- A relative path is safe when it is non-blank, not absolute, and never
escapes the sandbox root via `..` or an empty/`.`-only segment. Pure and total;
the effectful ops call this before touching the filesystem. -/
public def safeRelPath (p : String) : Bool :=
  nonemptyText p &&
    !p.startsWith "/" &&
    !(p.startsWith "~") &&
    let segs := (p.splitOn "/").filter (fun s => s != "")
    !segs.isEmpty &&
    segs.all (fun s => s != ".." && s != ".")

/-- Resolve a sandbox-relative path against `root`, refusing unsafe paths. -/
public def resolve (root : System.FilePath) (rel : String) : Option System.FilePath :=
  if safeRelPath rel then some (root / rel) else none

/-- Read a file inside the sandbox. Returns a readable message on any failure;
never throws, so the result is always recordable as a tool observation. -/
public def readFileIn (root : System.FilePath) (rel : String) : IO String := do
  match resolve root rel with
  | none => pure s!"read_file: unsafe or blank path `{rel}`"
  | some path =>
    let exists? ← path.pathExists
    if !exists? then
      pure s!"read_file: not found `{rel}`"
    else
      let isDir ← path.isDir
      if isDir then
        pure s!"read_file: `{rel}` is a directory"
      else
        try
          let contents ← IO.FS.readFile path
          pure contents
        catch e =>
          pure s!"read_file error: {e.toString}"

/-- List a directory inside the sandbox (or the root itself when `rel` is "."). -/
public def listDirIn (root : System.FilePath) (rel : String) : IO String := do
  let dir? : Option System.FilePath :=
    if rel == "." || !nonemptyText rel then some root else resolve root rel
  match dir? with
  | none => pure s!"list_dir: unsafe path `{rel}`"
  | some path =>
    let exists? ← path.pathExists
    if !exists? then
      pure s!"list_dir: not found `{rel}`"
    else
      try
        let entries ← path.readDir
        let names := entries.toList.map (fun e => e.fileName)
        if names.isEmpty then pure "list_dir: (empty)"
        else pure (joinSep "\n" names)
      catch e =>
        pure s!"list_dir error: {e.toString}"

/-- Write a file inside the sandbox, creating parent directories. Gated by
`safeRelPath`; the caller decides whether to expose this at all (a reader agent
simply never offers a write tool). -/
public def writeFileIn (root : System.FilePath) (rel content : String) : IO String := do
  match resolve root rel with
  | none => pure s!"write_file: unsafe or blank path `{rel}`"
  | some path =>
    try
      match path.parent with
      | some parent => IO.FS.createDirAll parent
      | none => pure ()
      IO.FS.writeFile path content
      pure s!"wrote {content.utf8ByteSize} bytes to {rel}"
    catch e =>
      pure s!"write_file error: {e.toString}"

#guard safeRelPath "notes/summary.json"
#guard safeRelPath "a.txt"
#guard !safeRelPath "/etc/passwd"
#guard !safeRelPath "../secret"
#guard !safeRelPath "a/../../b"
#guard !safeRelPath "~/private"
#guard !safeRelPath "   "
#guard !safeRelPath "."
#guard
  match resolve ⟨"/tmp/sandbox"⟩ "out/report.json" with
  | some p => p.toString == "/tmp/sandbox/out/report.json"
  | none => false
#guard (resolve ⟨"/tmp/sandbox"⟩ "../escape").isNone

end

end LeanAgent.Files
