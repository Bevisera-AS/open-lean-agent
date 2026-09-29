module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Json
public import LeanAgent.ToolSpec
public import LeanAgent.Anthropic
public meta import LeanAgent.Json
public meta import LeanAgent.ToolSpec
public meta import LeanAgent.Anthropic

namespace LeanAgent

open Lean

public section

public def encodeMessage (m : Message) : Json :=
  let content : Json :=
    match m.toolCallsJson? with
    | some _ =>
      if nonemptyText m.content then Json.str m.content else Json.null
    | none => Json.str m.content
  let fields : List (String × Json) := [
    ("role", Json.str m.role.toWire),
    ("content", content)
  ]
  let fields :=
    match m.toolCallId? with
    | some id => fields ++ [("tool_call_id", Json.str id)]
    | none => fields
  let fields :=
    match m.toolCallsJson? with
    | some s =>
      match Json.parse s with
      | .ok j => fields ++ [("tool_calls", j)]
      | .error _ => fields
    | none => fields
  Json.mkObj fields

/-- OpenAI Chat Completions body. Secrets never belong here.
Anthropic uses Messages encoding: no `response_format`; the schema is a system instruction. -/
public def chatRequest (cfg : ProviderConfig) (msgs : Array Message) (schema : Json)
    (schemaName : String) (tools : Array ToolSpec := #[]) : Json :=
  match cfg.protocol with
  | .anthropicMessages =>
    anthropicRequest cfg msgs (schemaSystem schemaName schema) tools
  | .openAIChat =>
    let format := Json.mkObj [
      ("type", Json.str "json_schema"),
      ("json_schema", Json.mkObj [
        ("name", Json.str schemaName),
        ("strict", Json.bool true),
        ("schema", schema)
      ])
    ]
    let fields : List (String × Json) := [
      ("model", Json.str cfg.model),
      ("messages", Json.arr (msgs.map encodeMessage)),
      ("response_format", format)
    ]
    let fields :=
      match cfg.maxTokens with
      | some n => fields ++ [("max_tokens", (n : Json))]
      | none => fields
    let fields :=
      if tools.isEmpty then fields
      else fields ++ [("tools", Json.arr (tools.map encodeToolSpec))]
    Json.mkObj fields

/-- Ask / tool loop. No `json_schema`: the model may call a tool or answer in text. -/
public def chatRequestTools (cfg : ProviderConfig) (msgs : Array Message)
    (tools : Array ToolSpec) : Json :=
  match cfg.protocol with
  | .anthropicMessages =>
    anthropicRequest cfg msgs "" tools
  | .openAIChat =>
    let fields : List (String × Json) := [
      ("model", Json.str cfg.model),
      ("messages", Json.arr (msgs.map encodeMessage))
    ]
    let fields :=
      match cfg.maxTokens with
      | some n => fields ++ [("max_tokens", (n : Json))]
      | none => fields
    let fields :=
      if tools.isEmpty then fields
      else fields ++ [
        ("tools", Json.arr (tools.map encodeToolSpec)),
        ("tool_choice", Json.str "auto"),
        ("parallel_tool_calls", Json.bool false)
      ]
    Json.mkObj fields

public def wrapContent (content : String) : String :=
  Json.compress (Json.mkObj [
    ("choices", Json.arr #[Json.mkObj [
      ("finish_reason", Json.str "stop"),
      ("message", Json.mkObj [
        ("role", Json.str "assistant"),
        ("content", Json.str content)
      ])
    ]])
  ])

/-- Test envelope carrying `reasoning_content` alongside the final content. -/
public def wrapContentReasoning (reasoning content : String) : String :=
  Json.compress (Json.mkObj [
    ("choices", Json.arr #[Json.mkObj [
      ("finish_reason", Json.str "stop"),
      ("message", Json.mkObj [
        ("role", Json.str "assistant"),
        ("reasoning_content", Json.str reasoning),
        ("content", Json.str content)
      ])
    ]])
  ])

public def wrapContentTruncated (content : String) : String :=
  Json.compress (Json.mkObj [
    ("choices", Json.arr #[Json.mkObj [
      ("finish_reason", Json.str "length"),
      ("message", Json.mkObj [
        ("role", Json.str "assistant"),
        ("content", Json.str content)
      ])
    ]])
  ])

public def isTruncatedFinishReason : String → Bool
  | "length" | "max_tokens" => true
  | _ => false

public def openAIChoiceTruncated (choice : Json) : Bool :=
  match choice.getObjVal? "finish_reason" with
  | .ok v =>
    match v.getStr? with
    | .ok s => isTruncatedFinishReason s
    | .error _ => false
  | .error _ => false

public def anthropicMessageTruncated (raw : String) : Bool :=
  match Json.parse raw with
  | .error _ => false
  | .ok j =>
    match j.getObjVal? "stop_reason" with
    | .ok v =>
      match v.getStr? with
      | .ok "max_tokens" => true
      | _ => false
    | .error _ => false

public def completionTruncated (raw : String) (protocol : Protocol := .openAIChat) : Bool :=
  match protocol with
  | .anthropicMessages => anthropicMessageTruncated raw
  | .openAIChat =>
    match Json.parse raw with
    | .error _ => false
    | .ok j =>
      match j.getObjVal? "choices" with
      | .error _ => false
      | .ok choices =>
        match choices.getArr? with
        | .error _ => false
        | .ok arr =>
          match arr[0]? with
          | none => false
          | some choice => openAIChoiceTruncated choice

public def refuseIfTruncated (raw : String) (protocol : Protocol := .openAIChat) :
    Except DecodeError Unit :=
  if completionTruncated raw protocol then
    .error (.illFormed "completion" "truncated")
  else
    .ok ()

/-- Read an optional non-blank string field, tolerating null. Never fails: a
missing, null, or non-string value is simply `none`. Used for reasoning, which
is audit-only and always optional. -/
public def softStrField (j : Json) (key : String) : Option String :=
  match j.getObjVal? key with
  | .error _ => none
  | .ok v =>
    match v.getStr? with
    | .ok s => if nonemptyText s then some s else none
    | .error _ => none

/-- Provider reasoning trace, if the completion carried one. OpenAI-compatible
providers surface it as `choices[0].message.reasoning_content` (DeepSeek, vLLM,
some Ollama models) or `reasoning`; Anthropic uses `thinking` content blocks.
Absence is not an error — reasoning is optional and audit-only. -/
public def completionReasoning (raw : String) (protocol : Protocol := .openAIChat) :
    Option String :=
  match protocol with
  | .anthropicMessages => anthropicReasoning raw
  | .openAIChat =>
    match Json.parse raw with
    | .error _ => none
    | .ok j =>
      match j.getObjVal? "choices" with
      | .error _ => none
      | .ok choices =>
        match choices.getArr? with
        | .error _ => none
        | .ok arr =>
          match arr[0]? with
          | none => none
          | some choice =>
            match choice.getObjVal? "message" with
            | .error _ => none
            | .ok msg =>
              match softStrField msg "reasoning_content" with
              | some s => some s
              | none => softStrField msg "reasoning"

/-- Envelope extras (`id`, `usage`, …) are ignored. Payload extras are not. -/
public def messageContent (raw : String) (protocol : Protocol := .openAIChat) :
    Except DecodeError String :=
  match protocol with
  | .anthropicMessages => do
    refuseIfTruncated raw .anthropicMessages
    anthropicMessageContent raw
  | .openAIChat => do
    refuseIfTruncated raw .openAIChat
    let j ← parseJson raw
    let _ ← asObj "completion" j
    let choices ← arrField "completion" "choices" j
    match choices[0]? with
    | none => .error (.missingField "completion.choices" "0")
    | some choice => do
      let msg ← field "completion.choices[0]" "message" choice
      let content ← strField "completion.choices[0].message" "content" msg
      if nonemptyText content then
        pure content
      else
        .error (.illFormed "completion.choices[0].message.content" "blank")

/-- Token usage from a completion. OpenAI-compatible responses carry
`usage.{prompt_tokens, completion_tokens, total_tokens}`; Anthropic uses
`usage.{input_tokens, output_tokens}`. Best-effort: absence yields empty usage,
never an error. -/
public def completionUsage (raw : String) (protocol : Protocol := .openAIChat) : Usage :=
  match protocol with
  | .anthropicMessages => anthropicUsage raw
  | .openAIChat =>
    match Json.parse raw with
    | .error _ => {}
    | .ok j =>
      match j.getObjVal? "usage" with
      | .error _ => {}
      | .ok u =>
        { promptTokens := softNatField u "prompt_tokens"
          completionTokens := softNatField u "completion_tokens"
          totalTokens := softNatField u "total_tokens" }

#guard
  completionUsage "{\"choices\":[],\"usage\":{\"prompt_tokens\":11,\"completion_tokens\":7,\"total_tokens\":18}}"
    == { promptTokens := some 11, completionTokens := some 7, totalTokens := some 18 }
#guard (completionUsage "{\"choices\":[]}").isEmpty
#guard
  completionUsage "{\"usage\":{\"input_tokens\":5,\"output_tokens\":9}}" Protocol.anthropicMessages
    == { promptTokens := some 5, completionTokens := some 9, totalTokens := some 14 }

#guard completionReasoning (wrapContentReasoning "step by step" "answer") == some "step by step"
#guard (completionReasoning (wrapContent "answer")).isNone
#guard
  completionReasoning (wrapAnthropicThinking "deliberating" "pong") Protocol.anthropicMessages
    == some "deliberating"
#guard
  match messageContent (wrapContentReasoning "hidden" "answer") with
  | .ok "answer" => true
  | _ => false

end

end LeanAgent
