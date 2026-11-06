module

public import LeanAgent.Util
public import LeanAgent.JsonCore
public import LeanAgent.Provider
public meta import LeanAgent.Util
public meta import LeanAgent.JsonCore
public meta import LeanAgent.Provider

namespace LeanAgent

public section

public inductive Role where
  | system
  | user
  | assistant
  | tool
  deriving Repr, BEq, DecidableEq

public def Role.toWire : Role → String
  | .system => "system"
  | .user => "user"
  | .assistant => "assistant"
  | .tool => "tool"

public structure Message where
  role : Role
  content : String
  toolCallId? : Option String := none
  toolCallsJson? : Option String := none
  /-- The assistant turn's content blocks as the provider returned them, a compressed
  JSON array: for Anthropic, `thinking`, `redacted_thinking`, `text` and `tool_use`
  in the model's order. The Anthropic encoder replays it verbatim, so the signed
  thinking a turn's tool calls rest on reaches the model again; the OpenAI encoder
  ignores it, since Chat Completions carries no such blocks. -/
  contentBlocksJson? : Option String := none
  deriving Repr, BEq

public inductive ExtractError where
  | transport (detail : String)
  | refused (err : DecodeError) (attempts : Nat)
  | truncated
  | provider (code : String) (message : String)
  deriving Repr, BEq

public def ExtractError.pretty : ExtractError → String
  | .transport d => s!"transport: {d}"
  | .refused e n => s!"refused after {n} attempt(s): {e.pretty}"
  | .truncated => "truncated"
  | .provider code msg => s!"provider {code}: {msg}"

end

end LeanAgent
