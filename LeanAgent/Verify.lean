module

public import LeanAgent.Util
public meta import LeanAgent.Util

/-!
Verifier tools: compile Lean snippets and report the toolchain, by shelling out
to `lean` / `lake` (same discipline as `Curl`). A snippet check is an
*observation* — it runs external code at elaboration time — so it is written to
a temp directory, bounded by a wall-clock timeout, and never touches the live
project. The temp directory is not a sandbox for the code itself (see
`leanCheck`). Output is a structured verdict string, never an exception.
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

/-- Drain a pipe into `buf` chunk by chunk, so whatever the process wrote
before it was killed is kept even when the pipe is never closed. -/
private partial def drain (h : IO.FS.Handle) (buf : IO.Ref ByteArray) : IO Unit := do
  let chunk ← h.read 4096
  if chunk.isEmpty then return
  buf.modify (· ++ chunk)
  drain h buf

/-- Bytes as text; a chunk boundary can split a multi-byte character, so up to
three trailing bytes are dropped rather than failing. -/
private def textOf (bytes : ByteArray) : String :=
  let rec go (b : ByteArray) : Nat → String
    | 0 => ""
    | n + 1 =>
      match String.fromUTF8? b with
      | some s => s
      | none => if b.size == 0 then "" else go (b.extract 0 (b.size - 1)) n
  go bytes 4

/-- Stop the process group `pid` leads: `SIGTERM` through Lean (the child was
spawned with `setsid`, so `kill` reaches the whole group), then `SIGKILL` to the
group through the shell's built-in `kill`, which needs no `procps`. Every
descendant that stayed in the group goes, however deep; one that left it with
its own `setsid` does not, and `graceMs` bounds how long its pipe is waited on. -/
private def killGroup {cfg : IO.Process.StdioConfig} (child : IO.Process.Child cfg) : IO Unit := do
  try child.kill catch _ => pure ()
  IO.sleep 100
  try
    let _ ← IO.Process.output
      { cmd := "sh", args := #["-c", "kill -s KILL -- -$1", "sh", toString child.pid] }
  catch _ => pure ()

/-- Run a process bounded by `timeoutSecs`, in Lean: the child is spawned in its
own process group (`setsid`), polled, and past the deadline the whole group is
killed (`TERM`, then `KILL`), grandchildren included. The output is what was
read before then. The function returns within the deadline plus `graceMs`: a
process that left the group and still holds the pipe does not keep it waiting.
A child that exits while a descendant still holds the pipe is given until the
deadline for that descendant to finish, then the group is killed and the run
counts as timed out. Needs no `timeout` or `pgrep` binary. The spawn's `cwd`
is kept; stdin is closed. Shared by `leanCheck`, the builder tools
(`LeanAgent.Build`) and the spec loop's referee. -/
public def runBounded (spec : IO.Process.SpawnArgs) (timeoutSecs : Nat) (graceMs : Nat := 2000) :
    IO (IO.Process.Output × Bool) := do
  let child ← IO.Process.spawn
    { spec with stdin := .null, stdout := .piped, stderr := .piped, setsid := true }
  let outBuf ← IO.mkRef ByteArray.empty
  let errBuf ← IO.mkRef ByteArray.empty
  let outTask ← IO.asTask (drain child.stdout outBuf)
  let errTask ← IO.asTask (drain child.stderr errBuf)
  let drained : IO Bool := do pure ((← IO.hasFinished outTask) && (← IO.hasFinished errTask))
  let deadline := (← IO.monoMsNow) + timeoutSecs * 1000
  let mut timedOut := false
  -- `tryWait` reaps the child when it has exited, so its code is kept here and
  -- `wait` is only called after a kill.
  let mut exited? : Option UInt32 := none
  repeat
    if exited?.isNone then
      exited? ← child.tryWait
    if exited?.isSome && (← drained) then
      break
    if (← IO.monoMsNow) ≥ deadline then
      timedOut := true
      killGroup child
      break
    IO.sleep 50
  let exitCode ← match exited? with
    | some code => pure code
    | none => child.wait
  -- After a kill the pipes close as the group dies; a holder that escaped the
  -- group is not waited on past the grace.
  let grace := (← IO.monoMsNow) + graceMs
  while timedOut && !(← drained) && (← IO.monoMsNow) < grace do
    IO.sleep 10
  let stdout := textOf (← outBuf.get)
  let stderr := textOf (← errBuf.get)
  pure ({ exitCode, stdout, stderr }, timedOut)

/-- Run `lean` on a snippet written to a temp file, bounded by `timeoutSecs`.
Uses the ambient toolchain via `lake env lean`. Best-effort: any process
failure becomes a `FAIL` verdict, never an exception.

The temp directory confines the file, not the snippet: elaboration runs `IO`,
so a snippet is arbitrary code on this host with this user's rights. A
verifier for hostile snippets needs an OS sandbox around the process. -/
public def leanCheck (code : String) (timeoutSecs : Nat := 30) : IO Verdict := do
  if !nonemptyText code then
    return { ok := false, detail := "empty snippet" }
  IO.FS.withTempDir fun dir => do
    let file := dir / "Snippet.lean"
    IO.FS.writeFile file code
    let (out, timedOut) ← runBounded { cmd := "lake", args := #["env", "lean", file.toString] } timeoutSecs
    if out.exitCode == 0 then
      pure { ok := true, detail := clip out.stdout }
    else if timedOut then
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
