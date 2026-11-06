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

@[expose] public def anthropicToolResultBlock (callId output : String) : Json :=
  Json.mkObj [
    ("type", Json.str "tool_result"),
    ("tool_use_id", Json.str callId),
    ("content", Json.str output)
  ]

/-- The `tool_result` block of a tool message. -/
@[expose] public def anthropicToolResultBlockOf (m : Message) : Json :=
  anthropicToolResultBlock (m.toolCallId?.getD "") m.content

/-- A user message whose content is `blocks`. -/
public def anthropicUserMessage (blocks : List Json) : Json :=
  Json.mkObj [("role", Json.str "user"), ("content", Json.arr blocks.toArray)]

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
    -- A turn the model produced goes back as it came, thinking blocks included;
    -- one built by hand is synthesized from its text and calls.
    match m.contentBlocksJson?.bind fun s => (Json.parse s).toOption.bind (·.getArr?.toOption) with
    | some blocks =>
      Json.mkObj [("role", Json.str "assistant"), ("content", Json.arr blocks)]
    | none =>
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
  | .tool => anthropicUserMessage [anthropicToolResultBlockOf m]

/-- `pending` tool results not yet sent, flushed as one user message ahead of `tail`. -/
public def anthropicFlush (pending tail : List Json) : List Json :=
  if pending.isEmpty then tail else anthropicUserMessage pending :: tail

public def anthropicMessagesGo (pending : List Json) : List Message → List Json
  | [] => anthropicFlush pending []
  | m :: rest =>
    if m.role = .tool then anthropicMessagesGo (pending ++ [anthropicToolResultBlockOf m]) rest
    else anthropicFlush pending (encodeAnthropicMessage m :: anthropicMessagesGo [] rest)

/-- The conversation as the Messages API wants it, which is not one message per
`Message`. An assistant turn that asks for several tools is answered by a single
user message carrying one `tool_result` block per call, and roles alternate; so a
run of consecutive tool messages becomes one message, in order, and everything
else maps as it reads. `anthropicMessagesGo_batches` is that rule as a theorem. -/
public def anthropicMessageList (msgs : List Message) : List Json :=
  anthropicMessagesGo [] msgs

theorem anthropicFlush_nil (tail : List Json) : anthropicFlush [] tail = tail := by
  simp [anthropicFlush]

theorem anthropicFlush_append (pending tail tail' : List Json) :
    anthropicFlush pending (tail ++ tail') = anthropicFlush pending tail ++ tail' := by
  unfold anthropicFlush
  split <;> simp

/-- A run of tool messages becomes the pending results, in order, and nothing else. -/
theorem anthropicMessagesGo_tools (pending : List Json) (ts : List Message)
    (h : ∀ m ∈ ts, m.role = .tool) :
    anthropicMessagesGo pending ts =
      anthropicFlush (pending ++ ts.map anthropicToolResultBlockOf) [] := by
  induction ts generalizing pending with
  | nil => simp [anthropicMessagesGo]
  | cons m rest ih =>
    have hm : m.role = .tool := h m (by simp)
    simp only [anthropicMessagesGo, ite_eq_left hm]
    rw [ih _ (fun x hx => h x (by simp [hx]))]
    simp [List.append_assoc]

/-- The results answering a turn go out as one user message, one `tool_result` block
per tool message in the order given, right after the turn they answer; the
messages before are encoded exactly as they would be without the results.
`a` is the turn being answered, any message that is not itself a tool result. -/
theorem anthropicMessagesGo_batches (pending : List Json) (before : List Message) (a : Message)
    (ha : a.role ≠ .tool) (ts : List Message) (hts : ∀ m ∈ ts, m.role = .tool) (hne : ts ≠ []) :
    anthropicMessagesGo pending (before ++ a :: ts) =
      anthropicMessagesGo pending (before ++ [a]) ++
        [anthropicUserMessage (ts.map anthropicToolResultBlockOf)] := by
  induction before generalizing pending with
  | nil =>
    simp only [List.nil_append, anthropicMessagesGo, ite_eq_right ha, anthropicFlush_nil]
    rw [anthropicMessagesGo_tools [] ts hts]
    have hts' : anthropicFlush ([] ++ ts.map anthropicToolResultBlockOf) [] =
        [anthropicUserMessage (ts.map anthropicToolResultBlockOf)] := by
      cases ts with
      | nil => exact absurd rfl hne
      | cons m rest => simp [anthropicFlush]
    rw [hts', ← anthropicFlush_append]
    rfl
  | cons b before' ih =>
    simp only [List.cons_append, anthropicMessagesGo]
    by_cases hb : b.role = .tool
    · simp only [ite_eq_left hb]
      exact ih _
    · simp only [ite_eq_right hb]
      rw [ih, ← anthropicFlush_append]
      rfl

theorem anthropicMessageList_batches (before : List Message) (a : Message) (ha : a.role ≠ .tool)
    (ts : List Message) (hts : ∀ m ∈ ts, m.role = .tool) (hne : ts ≠ []) :
    anthropicMessageList (before ++ a :: ts) =
      anthropicMessageList (before ++ [a]) ++
        [anthropicUserMessage (ts.map anthropicToolResultBlockOf)] :=
  anthropicMessagesGo_batches [] before a ha ts hts hne

-- Two results after a tool-calling turn go out as one user message; the rest map one to one.
#guard
  let msgs : List Message := [
    { role := .user, content := "hi" },
    { role := .assistant, content := "", toolCallsJson? := some "[]" },
    { role := .tool, content := "1", toolCallId? := some "a" },
    { role := .tool, content := "2", toolCallId? := some "b" },
    { role := .user, content := "go on" }
  ]
  (anthropicMessageList msgs).map Json.compress == [
    "{\"content\":\"hi\",\"role\":\"user\"}",
    "{\"content\":[],\"role\":\"assistant\"}",
    "{\"content\":[{\"content\":\"1\",\"tool_use_id\":\"a\",\"type\":\"tool_result\"}," ++
      "{\"content\":\"2\",\"tool_use_id\":\"b\",\"type\":\"tool_result\"}],\"role\":\"user\"}",
    "{\"content\":\"go on\",\"role\":\"user\"}"
  ]
#guard (anthropicMessageList []).isEmpty

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
    ("messages", Json.arr (anthropicMessageList rest.toList).toArray)
  ]
  let fields :=
    if nonemptyText sys then fields ++ [("system", Json.str sys)] else fields
  let fields :=
    match cfg.thinkingBudget with
    | some n => fields ++ [("thinking", Json.mkObj [
        ("type", Json.str "enabled"),
        ("budget_tokens", (n : Json))
      ])]
    | none => fields
  let fields :=
    if tools.isEmpty then fields
    else fields ++ [
      ("tools", Json.arr (tools.map encodeAnthropicToolSpec)),
      ("tool_choice", Json.mkObj [("type", Json.str "auto")])
    ]
  Json.mkObj fields

/-- Test envelope: an Anthropic message with the given content blocks and stop reason. -/
public def wrapAnthropicMessage (content : Array Json) (stopReason : String) : String :=
  Json.compress (Json.mkObj [
    ("id", Json.str "msg_test"),
    ("type", Json.str "message"),
    ("role", Json.str "assistant"),
    ("content", Json.arr content),
    ("stop_reason", Json.str stopReason)
  ])

public def anthropicTextBlock (text : String) : Json :=
  Json.mkObj [("type", Json.str "text"), ("text", Json.str text)]

/-- A signed `thinking` block as the API returns one. -/
public def anthropicThinkingBlock (thinking signature : String) : Json :=
  Json.mkObj [
    ("type", Json.str "thinking"),
    ("thinking", Json.str thinking),
    ("signature", Json.str signature)
  ]

public def anthropicToolUseBlock (id name argsJson : String) : Json :=
  let input :=
    match Json.parse argsJson with
    | .ok j => j
    | .error _ => Json.mkObj []
  Json.mkObj [
    ("type", Json.str "tool_use"),
    ("id", Json.str id),
    ("name", Json.str name),
    ("input", input)
  ]

public def wrapAnthropicText (content : String) : String :=
  wrapAnthropicMessage #[anthropicTextBlock content] "end_turn"

public def wrapAnthropicTruncated (content : String) : String :=
  wrapAnthropicMessage #[anthropicTextBlock content] "max_tokens"

/-- Test envelope: an Anthropic message whose content is the given
`(id, name, inputJson)` `tool_use` blocks, in order. -/
public def wrapAnthropicToolUses (uses : Array (String × String × String)) : String :=
  wrapAnthropicMessage (uses.map fun (id, name, argsJson) => anthropicToolUseBlock id name argsJson)
    "tool_use"

/-- Test envelope: a signed `thinking` block, then the `tool_use` blocks it led to,
as a thinking model asks for tools. -/
public def wrapAnthropicThinkingToolUses (thinking signature : String)
    (uses : Array (String × String × String)) : String :=
  wrapAnthropicMessage
    (#[anthropicThinkingBlock thinking signature] ++
      uses.map fun (id, name, argsJson) => anthropicToolUseBlock id name argsJson)
    "tool_use"

public def wrapAnthropicToolUse (id name argsJson : String) : String :=
  wrapAnthropicToolUses #[(id, name, argsJson)]

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

/-- The `type` of a content block, when it has one. -/
public def anthropicBlockType (j : Json) : Option String :=
  match j.getObjVal? "type" with
  | .ok ty => ty.getStr?.toOption
  | .error _ => none

/-- A block the Messages API returns for a request of ours and accepts back in an
assistant turn. An empty text block is refused by the API, and any other type is
not replayed. -/
public def anthropicReplayableBlock (j : Json) : Bool :=
  match anthropicBlockType j with
  | some "thinking" | some "redacted_thinking" | some "tool_use" => true
  | some "text" => (anthropicTextOfBlock j).any nonemptyText
  | _ => false

/-- The content of an Anthropic message as the model produced it, kept to the blocks
`anthropicReplayableBlock` admits and compressed, for `Message.contentBlocksJson?`.
The API checks each thinking block's signature against the blocks before it, so the
array keeps its order and its text unmerged. `none` when the message does not
decode or nothing in it is replayable. -/
public def anthropicReplayBlocks (raw : String) : Option String :=
  match anthropicContentBlocks raw with
  | .error _ => none
  | .ok blocks =>
    let kept := blocks.filter anthropicReplayableBlock
    if kept.isEmpty then none else some (Json.compress (Json.arr kept))

/-- The block types of a compressed content array, for tests. -/
public def anthropicBlockTypes (blocksJson : String) : Array String :=
  match Json.parse blocksJson with
  | .error _ => #[]
  | .ok j =>
    match j.getArr? with
    | .error _ => #[]
    | .ok arr => arr.filterMap anthropicBlockType

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

/-- Test envelope: a signed `thinking` block followed by a `text` block. -/
public def wrapAnthropicThinking (thinking content : String) (signature : String := "sig_test") :
    String :=
  wrapAnthropicMessage #[anthropicThinkingBlock thinking signature, anthropicTextBlock content]
    "end_turn"

-- A thinking turn is replayed in the model's order, signature included.
#guard
  let raw := wrapAnthropicThinkingToolUses "plan" "sig1" #[("t1", "echo", "{\"text\":\"a\"}")]
  match anthropicReplayBlocks raw with
  | some s =>
    anthropicBlockTypes s == #["thinking", "tool_use"] && s.contains "\"signature\":\"sig1\"" &&
      Json.compress (encodeAnthropicMessage { role := .assistant, content := "", contentBlocksJson? := some s }) ==
        "{\"content\":" ++ s ++ ",\"role\":\"assistant\"}"
  | none => false

-- Blocks of a type the API would not accept back, and empty text, are not replayed;
-- a message with nothing replayable yields `none`, and the encoder then synthesizes.
#guard
  let raw := wrapAnthropicMessage #[
    Json.mkObj [("type", Json.str "server_tool_use"), ("id", Json.str "x")],
    anthropicTextBlock "",
    Json.mkObj [("type", Json.str "redacted_thinking"), ("data", Json.str "opaque")],
    anthropicTextBlock "done"
  ] "end_turn"
  (anthropicReplayBlocks raw).map anthropicBlockTypes == some #["redacted_thinking", "text"]
#guard (anthropicReplayBlocks (wrapAnthropicMessage #[anthropicTextBlock ""] "end_turn")).isNone
#guard (anthropicReplayBlocks "not json").isNone
#guard
  Json.compress (encodeAnthropicMessage { role := .assistant, content := "hi", contentBlocksJson? := some "nope" }) ==
    "{\"content\":\"hi\",\"role\":\"assistant\"}"

-- The budget is requested only when set, and only by this encoder.
#guard
  let cfg : ProviderConfig := { anthropic with config := anthropic.config.withThinkingBudget (some 2048) }
  let body := Json.compress (anthropicRequest cfg #[{ role := .user, content := "hi" }])
  body.contains "\"thinking\":{\"budget_tokens\":2048,\"type\":\"enabled\"}"
#guard
  !(Json.compress (anthropicRequest anthropic #[{ role := .user, content := "hi" }])).contains "budget_tokens"

#guard
  anthropicReasoning (wrapAnthropicThinking "let me reason" "pong") == some "let me reason"

#guard (anthropicReasoning (wrapAnthropicText "pong")).isNone

#guard
  match anthropicMessageContent (wrapAnthropicThinking "hidden" "pong") with
  | .ok "pong" => true
  | _ => false

end

end LeanAgent
