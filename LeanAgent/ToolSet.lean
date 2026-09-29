module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.JsonCore
public import LeanAgent.Types
public import LeanAgent.ToolSpec
public meta import LeanAgent.JsonCore
public meta import LeanAgent.Types
public meta import LeanAgent.ToolSpec

namespace LeanAgent

open Lean

public section

/-- What effect a tool has on the knowledge store, along the capture → consolidate
→ approve → store axis:
* `read` — reads the store, changes nothing;
* `propose` — appends a candidate onto the agent/consolidation plane, pending a
  human approval;
* `commit` — promotes into the permanent store (the human-only action);
* `summarize` — a pure transformation of input (e.g. raw text → a candidate),
  touching no store at all;
* `verify` — runs a check/gate (e.g. a build or integrity check); reads to decide
  admission, but never proposes or commits.

Lets a caller state and check that an agent's catalog is confined to the effects
its *role* permits — and, in particular, contains no committing tool: the
human/agent gate as a property of the closed catalog. -/
public inductive ToolEffect
  | read | propose | commit | summarize | verify
  deriving Repr, BEq, DecidableEq

/-- Caller-owned closed tool algebra. A name that `decode` rejects cannot inhabit `invoke`. -/
public structure ToolSet (Tool : Type) where
  decode : String → Json → Except DecodeError Tool
  decodeTagged : Json → Except DecodeError Tool
  encodeTagged : Tool → Json
  name : Tool → String
  argumentsJson : Tool → Json
  specs : Array ToolSpec
  execute? : Tool → Option String
  isCite : Tool → Bool := fun _ => false
  usableCite : String → Bool := fun s => nonemptyText s
  /-- The effect classification of each tool. Defaults to `read`. -/
  effect : Tool → ToolEffect := fun _ => .read

public def ToolSet.encodeCall {Tool : Type} (ts : ToolSet Tool)
    (callId : String) (tool : Tool) : Json :=
  Json.mkObj [
    ("id", Json.str callId),
    ("type", Json.str "function"),
    ("function", Json.mkObj [
      ("name", Json.str (ts.name tool)),
      ("arguments", Json.str (Json.compress (ts.argumentsJson tool)))
    ])
  ]

public def ToolSet.assistantInvokeMessage {Tool : Type} (ts : ToolSet Tool)
    (callId : String) (tool : Tool) : Message := {
  role := .assistant
  content := ""
  toolCallsJson? := some (Json.compress (Json.arr #[ts.encodeCall callId tool]))
}

public def toolResultMessage (callId : String) (output : String) : Message := {
  role := .tool
  content := output
  toolCallId? := some callId
}

/-- Effectful counterpart of a `ToolSet`: how each decoded tool is actually run.
The agent loop calls `run` for tools whose `execute?` is `none` (observations). -/
public structure ToolRunner (Tool : Type) where
  run : Tool → IO String

end

end LeanAgent
