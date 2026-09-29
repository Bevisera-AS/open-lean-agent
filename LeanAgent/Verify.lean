module

public import LeanAgent.Util
public meta import LeanAgent.Util

/-!
Verifier tools: compile Lean snippets and report the toolchain, by shelling out
to `lean` / `lake` (same discipline as `Curl`). A snippet check is an
*observation* — it runs external code at elaboration time — so it is sandboxed
in a temp directory with a wall-clock timeout, and never touches the live
project. Output is a structured verdict string, never an exception.
-/

namespace LeanAgent.Verify

open LeanAgent

public section

/-- A compile verdict: whether `lean` accepted the snippet, plus trimmed
diagnostics. Pure so it can be formatted/tested without running a compiler. -/
public structure Verdict where
  ok : Bool
  detail : String
  deriving Repr, BEq

/-- First `n` characters of compiler output, so a verdict stays bounded. -/
public def clip (s : String) (n : Nat := 2000) : String :=
  (s.take n).toString

public def Verdict.render (v : Verdict) : String :=
  if v.ok then "OK: lean accepted the snippet"
  else "FAIL:\n" ++ v.detail

/-- Whether an executable is on `PATH` (via `which`). Best-effort. -/
public def checkBinary (name : String) : IO Bool := do
  try
    let out ← IO.Process.output { cmd := "which", args := #[name] }
    pure (out.exitCode == 0)
  catch _ =>
    pure false

/-- Run `lean` on a snippet written to a temp file, bounded by `timeoutSecs`.
Uses the ambient toolchain via `lake env lean`. Best-effort: any process
failure becomes a `FAIL` verdict, never an exception. -/
public def leanCheck (code : String) (timeoutSecs : Nat := 30) : IO Verdict := do
  if !nonemptyText code then
    return { ok := false, detail := "empty snippet" }
  IO.FS.withTempDir fun dir => do
    let file := dir / "Snippet.lean"
    IO.FS.writeFile file code
    -- Bound runaway elaboration with `timeout` when available (coreutils on
    -- Linux, `gtimeout` on macOS). Fall back to a direct call if neither exists.
    let hasTimeout ← checkBinary "timeout"
    let hasGtimeout ← checkBinary "gtimeout"
    let spec : IO.Process.SpawnArgs :=
      if hasTimeout then
        { cmd := "timeout", args := #[toString timeoutSecs, "lake", "env", "lean", file.toString] }
      else if hasGtimeout then
        { cmd := "gtimeout", args := #[toString timeoutSecs, "lake", "env", "lean", file.toString] }
      else
        { cmd := "lake", args := #["env", "lean", file.toString] }
    let out ← IO.Process.output spec
    if out.exitCode == 0 then
      pure { ok := true, detail := clip out.stdout }
    else if out.exitCode == 124 then
      pure { ok := false, detail := s!"timed out after {timeoutSecs}s" }
    else
      let diag := if nonemptyText out.stderr then out.stderr else out.stdout
      pure { ok := false, detail := clip diag }

/-- Report the active Lean toolchain (`lean --version`). -/
public def toolchain : IO String := do
  let out ← IO.Process.output { cmd := "lean", args := #["--version"] }
  if out.exitCode == 0 then pure out.stdout.trimAscii.copy
  else pure s!"lean --version failed (exit {out.exitCode})"

#guard (Verdict.render { ok := true, detail := "" }).startsWith "OK"
#guard (Verdict.render { ok := false, detail := "boom" }).startsWith "FAIL"
#guard clip "abcdef" 3 == "abc"

end

end LeanAgent.Verify
