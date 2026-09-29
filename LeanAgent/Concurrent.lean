module

public import LeanAgent.Agents
public meta import LeanAgent.Agents

/-!
Concurrency for the agent layer. Nothing here changes the bounded loop: agents
still run through `askWith`. These are thin wrappers over `IO.asTask`/`IO.wait`
so independent agents can run in parallel (e.g. a researcher drafting while a
verifier compiles the previous draft), plus a typed single-slot mailbox so a
produced Lean value crosses between agents *as a value*, not as a prompt string.
-/

namespace LeanAgent

public section

/-- A running agent: the `Task` of its eventual transcript. `IO.asTask` returns
`Except IO.Error _` because the background thread may throw. -/
public abbrev RunHandle (Tool : Type) := Task (Except IO.Error (Transcript Tool))

/-- Start an agent run on a background thread; returns immediately. -/
public def Agent.runInBackground {Tool : Type} (a : Agent Tool) (c : Completer)
    (prompt : String) (runId : String := "") : IO (RunHandle Tool) :=
  IO.asTask (a.run c prompt runId)

/-- Await a background run, re-raising any thread error into the current `IO`. -/
public def await {Tool : Type} (h : RunHandle Tool) : IO (Transcript Tool) := do
  match ← IO.wait h with
  | .ok t => pure t
  | .error e => throw e

/-- Run several independent agent actions concurrently and await them all,
preserving order. Each result carries its own thread error, if any. -/
public def fanOut {Tool : Type} (runs : Array (IO (Transcript Tool))) :
    IO (Array (Except IO.Error (Transcript Tool))) := do
  let handles ← runs.mapM (fun r => IO.asTask r)
  handles.mapM (fun h => do pure (← IO.wait h))

/-- Concurrent fan-out that re-raises the first thread error. -/
public def fanOutOrThrow {Tool : Type} (runs : Array (IO (Transcript Tool))) :
    IO (Array (Transcript Tool)) := do
  let results ← fanOut runs
  results.mapM fun
    | .ok t => pure t
    | .error e => throw e

/-!
## Typed mailbox

A single-slot, typed handoff channel. The producing agent posts a Lean `α`
(e.g. an `OutputContract` accept type); the consumer takes it. The value never
becomes a string in transit — only the caller decides to render it into a prompt
when it actually needs to talk to a model.
-/

public structure Mailbox (α : Type) where
  ref : IO.Ref (Option α)

public def Mailbox.new {α : Type} : IO (Mailbox α) := do
  pure { ref := ← IO.mkRef none }

/-- Place a value in the mailbox (overwriting any previous occupant). -/
public def Mailbox.post {α : Type} (m : Mailbox α) (value : α) : IO Unit :=
  m.ref.set (some value)

/-- Take the current value, if any, leaving the mailbox empty. -/
public def Mailbox.take? {α : Type} (m : Mailbox α) : IO (Option α) := do
  let v ← m.ref.get
  m.ref.set none
  pure v

/-- Peek without clearing. -/
public def Mailbox.peek? {α : Type} (m : Mailbox α) : IO (Option α) :=
  m.ref.get

end

end LeanAgent
