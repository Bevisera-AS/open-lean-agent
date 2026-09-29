module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Json
public import LeanAgent.ToolSpec
public import LeanAgent.Types
public import LeanAgent.Transport
public meta import LeanAgent.Json
public meta import LeanAgent.ToolSpec
public meta import LeanAgent.Types
public meta import LeanAgent.Transport

namespace LeanAgent

open Lean

public section

public def encodeAnthropicToolSpec (t : ToolSpec) : Json :=
  Json.mkObj [
    ("name", Json.str t.name),
    ("description", Json.str t.description),
    ("input_schema", t.parameters)
  ]

public def schemaSystem (schemaName : String) (schema : Json) : String :=
  "Return only JSON for `" ++ schemaName ++
    "` matching this schema. No markdown fences.\n" ++ schema.pretty

private def openaiCallToToolUse (j : Json) : Option Json :=
  match j.getObjVal? "id", j.getObjVal? "function" with
  | .ok idJ, .ok fn =>
    match idJ.getStr?, fn.getObjVal? "name", fn.getObjVal? "arguments" with
    | .ok id, .ok nameJ, .ok args =>
      match nameJ.getStr? with
      | .ok name =>
        let input :=
          match args.getStr? with
          | .ok s =>
            match Json.parse s with
            | .ok p => p
            | .error _ => Json.mkObj []
          | .error _ => args
        some (Json.mkObj [
          ("type", Json.str "tool_use"),
          ("id", Json.str id),
          ("name", Json.str name),
          ("input", input)
        ])
      | .error _ => none
    | _, _, _ => none
  | _, _ => none

private def toolUseBlocks (toolCallsJson : String) : Array Json :=
  match Json.parse toolCallsJson with
  | .error _ => #[]
  | .ok j =>
    match j.getArr? with
    | .error _ => #[]
    | .ok arr => arr.filterMap openaiCallToToolUse

public def splitSystem (msgs : Array Message) : String × Array Message :=
  let systemParts :=
    msgs.filterMap fun m =>
      if m.role == .system && nonemptyText m.content then some m.content else none
  let rest := msgs.filter (fun m => m.role != .system)
  (joinSep "\n" systemParts.toList, rest)

public def encodeAnthropicMessage (m : Message) : Json :=
  match m.role with
  | .system =>
    Json.mkObj [("role", Json.str "user"), ("content", Json.str m.content)]
  | .user =>
    Json.mkObj [("role", Json.str "user"), ("content", Json.str m.content)]
  | .assistant =>
    match m.toolCallsJson? with
    | none =>
      Json.mkObj [("role", Json.str "assistant"), ("content", Json.str m.content)]
    | some s =>
      let uses := toolUseBlocks s
      let blocks :=
        if nonemptyText m.content then
          #[Json.mkObj [("type", Json.str "text"), ("text", Json.str m.content)]] ++ uses
        else uses
      Json.mkObj [("role", Json.str "assistant"), ("content", Json.arr blocks)]
  | .tool =>
    Json.mkObj [
      ("role", Json.str "user"),
      ("content", Json.arr #[Json.mkObj [
        ("type", Json.str "tool_result"),
        ("tool_use_id", Json.str (m.toolCallId?.getD "")),
        ("content", Json.str m.content)
      ]])
    ]

public def anthropicMaxTokens (cfg : ProviderConfig) : Nat :=
  cfg.maxTokens.getD 1024

public def anthropicRequest (cfg : ProviderConfig) (msgs : Array Message)
    (systemExtra : String := "") (tools : Array ToolSpec := #[]) : Json :=
  let (sys0, rest) := splitSystem msgs
  let sys :=
    match nonemptyText sys0, nonemptyText systemExtra with
    | true, true => sys0 ++ "\n" ++ systemExtra
    | true, false => sys0
    | false, true => systemExtra
    | false, false => ""
  let fields : List (String × Json) := [
    ("model", Json.str cfg.model),
    ("max_tokens", (anthropicMaxTokens cfg : Json)),
    ("messages", Json.arr (rest.map encodeAnthropicMessage))
  ]
  let fields :=
    if nonemptyText sys then fields ++ [("system", Json.str sys)] else fields
  let fields :=
    if tools.isEmpty then fields
    else fields ++ [
      ("tools", Json.arr (tools.map encodeAnthropicToolSpec)),
      ("tool_choice", Json.mkObj [("type", Json.str "auto")])
    ]
  Json.mkObj fields

public def wrapAnthropicText (content : String) : String :=
  Json.compress (Json.mkObj [
    ("id", Json.str "msg_test"),
    ("type", Json.str "message"),
    ("role", Json.str "assistant"),
    ("content", Json.arr #[Json.mkObj [
      ("type", Json.str "text"),
      ("text", Json.str content)
    ]]),
    ("stop_reason", Json.str "end_turn")
  ])

public def wrapAnthropicTruncated (content : String) : String :=
  Json.compress (Json.mkObj [
    ("id", Json.str "msg_test"),
    ("type", Json.str "message"),
    ("role", Json.str "assistant"),
    ("content", Json.arr #[Json.mkObj [
      ("type", Json.str "text"),
      ("text", Json.str content)
    ]]),
    ("stop_reason", Json.str "max_tokens")
  ])

public def wrapAnthropicToolUse (id name argsJson : String) : String :=
  let input :=
    match Json.parse argsJson with
    | .ok j => j
    | .error _ => Json.mkObj []
  Json.compress (Json.mkObj [
    ("id", Json.str "msg_test"),
    ("type", Json.str "message"),
    ("role", Json.str "assistant"),
    ("content", Json.arr #[Json.mkObj [
      ("type", Json.str "tool_use"),
      ("id", Json.str id),
      ("name", Json.str name),
      ("input", input)
    ]]),
    ("stop_reason", Json.str "tool_use")
  ])

public def anthropicContentBlocks (raw : String) : Except DecodeError (Array Json) := do
  let j ← parseJson raw
  let _ ← asObj "message" j
  arrField "message" "content" j

public def anthropicTextOfBlock (j : Json) : Option String :=
  match j.getObjVal? "type" with
  | .ok ty =>
    match ty.getStr? with
    | .ok "text" =>
      match j.getObjVal? "text" with
      | .ok t =>
        match t.getStr? with
        | .ok s => some s
        | .error _ => none
      | .error _ => none
    | _ => none
  | .error _ => none

public def decodeAnthropicToolUse (j : Json) : Except DecodeError (String × String × Json) := do
  let ctx := "message.content.tool_use"
  let ty ← strField ctx "type" j
  if ty != "tool_use" then
    .error (.invalidTag ctx "type" ty)
  else do
    let id ← strField ctx "id" j
    let name ← strField ctx "name" j
    let input ← field ctx "input" j
    if nonemptyText id then
      pure (id, name, input)
    else
      .error (.illFormed ctx "blank id")

public def anthropicMessageContent (raw : String) : Except DecodeError String := do
  let blocks ← anthropicContentBlocks raw
  let text :=
    joinSep "" (blocks.toList.filterMap anthropicTextOfBlock)
  if nonemptyText text then
    pure text
  else
    .error (.illFormed "message.content" "blank")

/-- Extended-thinking text of a `{"type":"thinking","thinking":"…"}` block, if any.
Reasoning is audit-only: a block without a thinking string contributes nothing. -/
public def anthropicThinkingOfBlock (j : Json) : Option String :=
  match j.getObjVal? "type" with
  | .ok ty =>
    match ty.getStr? with
    | .ok "thinking" =>
      match j.getObjVal? "thinking" with
      | .ok t =>
        match t.getStr? with
        | .ok s => if nonemptyText s then some s else none
        | .error _ => none
      | .error _ => none
    | _ => none
  | .error _ => none

/-- Concatenated extended-thinking text across content blocks. `none` when the
provider returned no thinking blocks (reasoning is optional, never required). -/
public def anthropicReasoning (raw : String) : Option String :=
  match anthropicContentBlocks raw with
  | .error _ => none
  | .ok blocks =>
    let think := joinSep "\n" (blocks.toList.filterMap anthropicThinkingOfBlock)
    if nonemptyText think then some think else none

/-- Read an optional `Nat` field, tolerating absence and non-numeric values.
Never fails: usage accounting is best-effort. -/
public def softNatField (j : Json) (key : String) : Option Nat :=
  match j.getObjVal? key with
  | .error _ => none
  | .ok v =>
    match v.getNat? with
    | .ok n => some n
    | .error _ => none

/-- Token usage from an Anthropic Messages response: `usage.input_tokens` /
`usage.output_tokens`. Anthropic reports no single total, so `totalTokens` is
the sum when both parts are present. -/
public def anthropicUsage (raw : String) : Usage :=
  match Json.parse raw with
  | .error _ => {}
  | .ok j =>
    match j.getObjVal? "usage" with
    | .error _ => {}
    | .ok u =>
      let input := softNatField u "input_tokens"
      let output := softNatField u "output_tokens"
      let total := match input, output with
        | some i, some o => some (i + o)
        | _, _ => none
      { promptTokens := input, completionTokens := output, totalTokens := total }

#guard
  let body := Json.compress (anthropicRequest anthropic #[{ role := .user, content := "hi" }])
  body.contains "claude-sonnet-4-5" &&
    body.contains "max_tokens" &&
    !body.contains "response_format" &&
    !body.contains "chat/completions" &&
    !body.contains "Bearer"

#guard
  let (sys, rest) := splitSystem #[
    { role := .system, content := "rules" },
    { role := .user, content := "hi" }
  ]
  sys == "rules" && rest.size == 1 &&
    (match rest[0]? with | some m => m.role == .user | none => false)

#guard
  match anthropicMessageContent (wrapAnthropicText "pong") with
  | .ok "pong" => true
  | _ => false

/-- Test envelope: a leading `thinking` block followed by a `text` block. -/
public def wrapAnthropicThinking (thinking content : String) : String :=
  Json.compress (Json.mkObj [
    ("id", Json.str "msg_test"),
    ("type", Json.str "message"),
    ("role", Json.str "assistant"),
    ("content", Json.arr #[
      Json.mkObj [("type", Json.str "thinking"), ("thinking", Json.str thinking)],
      Json.mkObj [("type", Json.str "text"), ("text", Json.str content)]
    ]),
    ("stop_reason", Json.str "end_turn")
  ])

#guard
  anthropicReasoning (wrapAnthropicThinking "let me reason" "pong") == some "let me reason"

#guard (anthropicReasoning (wrapAnthropicText "pong")).isNone

#guard
  match anthropicMessageContent (wrapAnthropicThinking "hidden" "pong") with
  | .ok "pong" => true
  | _ => false

end

end LeanAgent
