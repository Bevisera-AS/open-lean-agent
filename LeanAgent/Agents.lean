module

public import LeanAgent.Ask
public import LeanAgent.Extract
public import LeanAgent.Completer
public meta import LeanAgent.Ask
public meta import LeanAgent.Extract

/-!
Thin multi-agent sugar. An "agent" is not new machinery: it is just a bundle of
what `askWith` already takes — a closed `ToolSet`, a system prompt, a
`ProviderConfig`, and a `ToolRunner`. This module only packages that tuple and
adds helpers for running an agent and handing a *typed* result to the next one.

Handoff is Lean-typed, not markdown: a producing agent yields an `α` via an
`OutputContract` (the same fail-closed extract path), and the consuming agent
receives either the Lean value directly or its canonical JSON (`contract.encode`).
-/

namespace LeanAgent

open Lean

public section

/-- A role-scoped agent over a caller-owned closed tool type. -/
public structure Agent (Tool : Type) where
  name : String
  system : String
  cfg : ProviderConfig
  tools : ToolSet Tool
  runner : ToolRunner Tool
  policy : AskPolicy := {}

/-- Run an agent on a prompt, producing an audited transcript. `c` is the model
seam (`curlCompleter cfg` live, or a scripted `Completer` in tests). -/
public def Agent.run {Tool : Type} (a : Agent Tool) (c : Completer) (prompt : String)
    (runId : String := "") : IO (Transcript Tool) :=
  askWith a.tools a.system c a.cfg prompt a.policy a.runner runId

/-- Live convenience: build the curl completer from the agent's own config. -/
public def Agent.runLive {Tool : Type} (a : Agent Tool) (prompt : String)
    (runId : String := "") : IO (Transcript Tool) :=
  a.run (curlCompleter a.cfg) prompt runId

/-- The final text of a finished run, if any. `none` on refusal/transport/truncation. -/
public def Agent.finalText {Tool : Type} (t : Transcript Tool) : Option String :=
  finishText t

/-!
## Typed handoff

`extractTyped` runs the structured-output path and returns a Lean value `α` (or a
typed `ExtractError`). Two ways to pass it on:

* `handoffValue` — keep it in Lean: transform `α` into the next agent's prompt
  with a caller-supplied function, so the boundary stays type-checked.
* `handoffJson`  — serialize via `contract.encode` and embed the canonical JSON
  in the next prompt (useful when the downstream agent should see the exact
  fields, or for logging the handoff).
-/

/-- Structured output as a Lean value, using the agent's provider/config. -/
public def extractTyped {α : Type} (contract : OutputContract α) (c : Completer)
    (cfg : ProviderConfig) (prompt : String) (policy : ExtractPolicy := {}) :
    IO (Except ExtractError α) :=
  contract.extract c cfg #[{ role := .user, content := prompt }] policy

/-- Hand a Lean value to the next step by rendering it into a prompt. The value
never round-trips through free text unless you choose to. -/
public def handoffValue {α : Type} (value : α) (render : α → String) : String :=
  render value

/-- Hand a value across as canonical JSON produced by the contract encoder. -/
public def handoffJson {α : Type} (contract : OutputContract α) (value : α) : String :=
  Json.compress (contract.encode value)

end

end LeanAgent
