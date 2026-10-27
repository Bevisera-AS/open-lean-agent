module

public import LeanAgent.Util
public meta import LeanAgent.Util

namespace LeanAgent.Files

open LeanAgent

public section

/-- `pathSegments`'s loop: `cur` is the segment being read (reversed), `acc`
the segments finished so far. Structural on the input, so no termination proof. -/
@[expose] public def pathSegmentsGo : List Char → List Char → List (List Char) → List (List Char)
  | [], cur, acc => acc ++ (if cur.isEmpty then [] else [cur.reverse])
  | '/' :: rest, cur, acc => pathSegmentsGo rest [] (acc ++ (if cur.isEmpty then [] else [cur.reverse]))
  | c :: rest, cur, acc => pathSegmentsGo rest (c :: cur) acc

/-- The `/`-separated segments of a path, as character lists, empty ones
dropped. Over lists so `safeRelPath` is decidable by the kernel. -/
@[expose] public def pathSegments (cs : List Char) : List (List Char) :=
  pathSegmentsGo cs [] []

/-- A relative path is safe when it is non-blank, not absolute, and never
escapes the sandbox root via `..` or an empty/`.`-only segment. Pure, total and
lexical: it does not see symlinks, which `confine` checks before any effect. -/
@[expose] public def safeRelPath (p : String) : Bool :=
  let cs := p.toList
  nonemptyText p &&
    cs.head? != some '/' &&
    cs.head? != some '~' &&
    let segs := pathSegments cs
    !segs.isEmpty &&
    segs.all (fun s => s != ['.', '.'] && s != ['.'])

/-- Resolve a sandbox-relative path against `root`, refusing unsafe paths. -/
public def resolve (root : System.FilePath) (rel : String) : Option System.FilePath :=
  if safeRelPath rel then some (root / rel) else none

/-- Whether `p` is itself a symlink (not following it). False when `p` is absent. -/
private def isSymlink (p : System.FilePath) : IO Bool := do
  try pure ((← p.symlinkMetadata).type == .symlink) catch _ => pure false

/-- The nearest existing ancestor of `p` (`p` itself when it exists), stepping
up through at most `fuel` parents. -/
private partial def existingAncestor (p : System.FilePath) (fuel : Nat) : IO System.FilePath := do
  if fuel == 0 then return p
  if ← p.pathExists then return p
  match p.parent with
  | some parent => existingAncestor parent (fuel - 1)
  | none => return p

/-- `resolve`, then the check the lexical rule cannot make: with symlinks
followed, the real path of `rel` must still lie under the real root. For a path
that does not exist yet (a write), its nearest existing ancestor is checked, and
a dangling symlink at the leaf is refused rather than written through. `none`
when the path escapes or cannot be resolved. The effectful ops call this, so a
symlink inside the sandbox cannot point a read, list or write outside it. -/
public def confine (root : System.FilePath) (rel : String) : IO (Option System.FilePath) := do
  let some path := resolve root rel | return none
  try
    let rootReal ← IO.FS.realPath root
    let exists? ← path.pathExists
    if !exists? && (← isSymlink path) then return none
    let anchor ← existingAncestor path path.components.length
    let real ← IO.FS.realPath anchor
    if rootReal.components.isPrefixOf real.components then pure (some path) else pure none
  catch _ => pure none

/-- Read a file inside the sandbox. Returns a readable message on any failure;
never throws, so the result is always recordable as a tool observation. -/
public def readFileIn (root : System.FilePath) (rel : String) : IO String := do
  match ← confine root rel with
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
  let dir? : Option System.FilePath ←
    if rel == "." || !nonemptyText rel then pure (some root) else confine root rel
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
  match ← confine root rel with
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

/-! The lexical rule, as theorems the kernel re-checks under `lake check`. -/

public theorem safeRelPath_accepts_nested : safeRelPath "notes/summary.json" = true := by decide
public theorem safeRelPath_accepts_flat : safeRelPath "a.txt" = true := by decide
public theorem safeRelPath_rejects_absolute : safeRelPath "/etc/passwd" = false := by decide
public theorem safeRelPath_rejects_parent : safeRelPath "../secret" = false := by decide
public theorem safeRelPath_rejects_nested_parent : safeRelPath "a/../../b" = false := by decide
public theorem safeRelPath_rejects_home : safeRelPath "~/private" = false := by decide
public theorem safeRelPath_rejects_blank : safeRelPath "   " = false := by decide
public theorem safeRelPath_rejects_dot : safeRelPath "." = false := by decide
public theorem safeRelPath_rejects_trailing_parent : safeRelPath "a/.." = false := by decide
public theorem pathSegments_drops_empty :
    pathSegments "a//b/".toList = [['a'], ['b']] := by decide
#guard
  match resolve ⟨"/tmp/sandbox"⟩ "out/report.json" with
  | some p => p.toString == "/tmp/sandbox/out/report.json"
  | none => false
#guard (resolve ⟨"/tmp/sandbox"⟩ "../escape").isNone

end

end LeanAgent.Files
