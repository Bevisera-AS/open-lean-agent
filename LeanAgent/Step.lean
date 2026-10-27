module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Tools
public import LeanAgent.Anthropic
public import LeanAgent.OpenAICompat
public meta import LeanAgent.Tools
public meta import LeanAgent.Anthropic
public meta import LeanAgent.OpenAICompat

namespace LeanAgent

open Lean

public section

/-- A decoded model move: one call per turn. Invented tool names never inhabit
`invoke`. `ModelTurn` is the same decoding without the one-call limit. -/
public inductive ModelStep (Tool : Type := DemoTool) where
  | finish (content : String)
  | invoke (callId : String) (tool : Tool)
  deriving Repr, BEq

/-- A decoded model turn: a text finish, or every tool call of one completion in
the order the model issued them. `invoke` is never empty and carries no invented
tool name, blank call id or duplicate call id. One call is the common case; several
is what an OpenAI-compatible provider returns as parallel `tool_calls` (GLM does so
even with `parallel_tool_calls` off) and Anthropic as several `tool_use` blocks. -/
public inductive ModelTurn (Tool : Type := DemoTool) where
  | finish (content : String)
  | invoke (calls : Array (String × Tool))
  deriving Repr, BEq

/-- Call ids within one turn are pairwise distinct, so each tool result answers
exactly one call. -/
public def distinctCallIds {Tool : Type} (calls : Array (String × Tool)) : Bool :=
  let ids := (calls.map (·.1)).toList
  ids.eraseDups.length == ids.length

/-- The calls of one completion as a turn; empty or ambiguous call lists fail. -/
public def turnOfCalls {Tool : Type} (ctx : String) (calls : Array (String × Tool)) :
    Except DecodeError (ModelTurn Tool) :=
  if calls.isEmpty then .error (.illFormed ctx "no tool calls")
  else if !distinctCallIds calls then .error (.illFormed ctx "duplicate call id")
  else .ok (.invoke calls)

/-- Where a protocol carries its tool calls, for error contexts. -/
public def toolCallsContext : Protocol → String
  | .openAIChat => "completion.choices[0].message.tool_calls"
  | .anthropicMessages => "message.content"

/-- The one move of a turn. A turn with several calls is refused with
`more than one tool call`, as before multi-call support; `askWith` runs on
`ModelTurn` and does not go through this. -/
public def ModelTurn.single {Tool : Type} (ctx : String) :
    ModelTurn Tool → Except DecodeError (ModelStep Tool)
  | .finish content => .ok (.finish content)
  | .invoke calls =>
    match calls[0]? with
    | none => .error (.illFormed ctx "no tool calls")
    | some (id, tool) =>
      if calls.size == 1 then .ok (.invoke id tool)
      else .error (.illFormed ctx "more than one tool call")

/-- Test envelope: an OpenAI Chat completion whose message carries the given
`(id, name, argumentsJson)` calls, in order. -/
public def wrapToolCalls (calls : Array (String × String × String)) : String :=
  Json.compress (Json.mkObj [
    ("choices", Json.arr #[Json.mkObj [
      ("finish_reason", Json.str "tool_calls"),
      ("message", Json.mkObj [
        ("role", Json.str "assistant"),
        ("content", Json.null),
        ("tool_calls", Json.arr (calls.map fun (id, name, argsJson) => Json.mkObj [
          ("id", Json.str id),
          ("type", Json.str "function"),
          ("function", Json.mkObj [
            ("name", Json.str name),
            ("arguments", Json.str argsJson)
          ])
        ]))
      ])
    ]])
  ])

public def wrapToolCall (id name argsJson : String) : String :=
  wrapToolCalls #[(id, name, argsJson)]

public def decodeArguments (fnCtx : String) (fn : Json) : Except DecodeError Json := do
  let argsVal ← field fnCtx "arguments" fn
  match argsVal.getStr? with
  | .ok s => parseJson s
  | .error _ =>
    match argsVal.getObj? with
    | .ok _ => pure argsVal
    | .error _ => .error (.wrongType fnCtx "arguments" "string or object")

public def decodeFunctionCallWith {Tool : Type} (ts : ToolSet Tool) (j : Json) :
    Except DecodeError (String × Tool) := do
  let ctx := "tool_call"
  let o ← asObj ctx j
  exactFields ctx ["id", "type", "function", "index"] o
  let ty := (← optStrField ctx "type" j).getD "function"
  if ty != "function" then
    .error (.invalidTag ctx "type" ty)
  else do
    let fn ← field ctx "function" j
    let fnCtx := s!"{ctx}.function"
    let fnObj ← asObj fnCtx fn
    exactFields fnCtx ["name", "arguments"] fnObj
    let name ← strField fnCtx "name" fn
    let args ← decodeArguments fnCtx fn
    let tool ← ts.decode name args
    let id := (← optStrField ctx "id" j).getD s!"call-{ts.name tool}"
    if nonemptyText id then pure (id, tool)
    else .error (.illFormed ctx "blank id")

public def decodeFunctionCall (j : Json) : Except DecodeError (String × DemoTool) :=
  decodeFunctionCallWith kernelTools j

public def isAnthropicToolUse (b : Json) : Bool :=
  match b.getObjVal? "type" with
  | .ok t =>
    match t.getStr? with
    | .ok "tool_use" => true
    | _ => false
  | .error _ => false

/-- Every `tool_use` block of an Anthropic message, decoded against the catalog;
text blocks are the finish when there is no `tool_use`. -/
public def turnFromAnthropicWith {Tool : Type} (ts : ToolSet Tool) (raw : String) :
    Except DecodeError (ModelTurn Tool) := do
  let blocks ← anthropicContentBlocks raw
  let uses := blocks.filter isAnthropicToolUse
  if uses.isEmpty then
    let text := joinSep "" (blocks.toList.filterMap anthropicTextOfBlock)
    if nonemptyText text then pure (.finish text)
    else .error (.illFormed "message.content" "blank")
  else
    let calls ← uses.mapM fun call => do
      let (id, name, input) ← decodeAnthropicToolUse call
      let tool ← ts.decode name input
      pure (id, tool)
    turnOfCalls (toolCallsContext .anthropicMessages) calls

public def stepFromAnthropicWith {Tool : Type} (ts : ToolSet Tool) (raw : String) :
    Except DecodeError (ModelStep Tool) := do
  (← turnFromAnthropicWith ts raw).single (toolCallsContext .anthropicMessages)

/-- Every tool call of a completion, or its text finish. Fails closed on a
truncated completion, an invented tool name, bad arguments, a blank or duplicate
call id, and a message with neither calls nor content. -/
public def turnFromCompletionWith {Tool : Type} (ts : ToolSet Tool) (raw : String)
    (protocol : Protocol := .openAIChat) : Except DecodeError (ModelTurn Tool) :=
  match refuseIfTruncated raw protocol with
  | .error e => .error e
  | .ok () =>
    match protocol with
    | .anthropicMessages => turnFromAnthropicWith ts raw
    | .openAIChat => do
    let j ← parseJson raw
    let _ ← asObj "completion" j
    let choices ← arrField "completion" "choices" j
    match choices[0]? with
    | none => .error (.missingField "completion.choices" "0")
    | some choice => do
      let msg ← field "completion.choices[0]" "message" choice
      match msg.getObjVal? "tool_calls" with
      | .ok callsJson =>
        let calls ←
          match callsJson.getArr? with
          | .ok a => pure a
          | .error _ => .error (.wrongType "completion.choices[0].message" "tool_calls" "array")
        if calls.isEmpty then
          let content? ← optNullableStrField "completion.choices[0].message" "content" msg
          match content? with
          | some c =>
            if nonemptyText c then pure (.finish c)
            else .error (.illFormed "completion.choices[0].message.content" "blank")
          | none => .error (.illFormed "completion.choices[0].message" "no tool_calls or content")
        else
          let decoded ← calls.mapM (decodeFunctionCallWith ts)
          turnOfCalls (toolCallsContext .openAIChat) decoded
      | .error _ => do
        let content ← strField "completion.choices[0].message" "content" msg
        if nonemptyText content then pure (.finish content)
        else .error (.illFormed "completion.choices[0].message.content" "blank")

/-- The one move of a completion. Same decoding as `turnFromCompletionWith`, and
a completion with several tool calls is refused. -/
public def stepFromCompletionWith {Tool : Type} (ts : ToolSet Tool) (raw : String)
    (protocol : Protocol := .openAIChat) : Except DecodeError (ModelStep Tool) := do
  (← turnFromCompletionWith ts raw protocol).single (toolCallsContext protocol)

public def stepFromCompletion (raw : String) : Except DecodeError (ModelStep DemoTool) :=
  stepFromCompletionWith kernelTools raw

public def dispatchWith {Tool : Type} (ts : ToolSet Tool) : ModelStep Tool → String
  | .finish content => content
  | .invoke _id tool => (ts.execute? tool).getD ""

public def dispatch : ModelStep DemoTool → String :=
  dispatchWith kernelTools

#guard
  match stepFromCompletion (wrapToolCall "c1" "echo" "{\"text\":\"hi\"}") with
  | .ok s => dispatch s == "hi"
  | .error _ => false

#guard
  match stepFromCompletion (wrapToolCall "c2" "show" "{\"name\":\"theme.selection\"}") with
  | .error (.invalidTag "tool" "name" "show") => true
  | _ => false

#guard
  match stepFromCompletion (wrapToolCall "c3" "shell" "{\"cmd\":\"rm\"}") with
  | .error (.invalidTag "tool" "name" "shell") => true
  | _ => false

#guard
  match stepFromCompletion (wrapToolCall "c4" "arxiv_search" "{\"query\":\"lean 4\"}") with
  | .ok (.invoke "c4" (.arxivSearch "lean 4")) => true
  | _ => false

/-- Two echo calls in one OpenAI Chat completion, as GLM returns them. -/
public def twoEchoCalls : String :=
  wrapToolCalls #[("c1", "echo", "{\"text\":\"a\"}"), ("c2", "echo", "{\"text\":\"b\"}")]

-- One move per turn: two calls are refused by `stepFromCompletion` …
#guard
  match stepFromCompletion twoEchoCalls with
  | .error (.illFormed "completion.choices[0].message.tool_calls" "more than one tool call") => true
  | _ => false

-- … and decoded in order by `turnFromCompletionWith`.
#guard
  match turnFromCompletionWith kernelTools twoEchoCalls with
  | .ok (.invoke #[("c1", .echo "a"), ("c2", .echo "b")]) => true
  | _ => false

-- A single call is the same turn either way.
#guard
  match turnFromCompletionWith kernelTools (wrapToolCall "c4" "arxiv_search" "{\"query\":\"lean 4\"}") with
  | .ok (.invoke #[("c4", .arxivSearch "lean 4")]) => true
  | _ => false

-- One invented name refuses the whole turn; nothing in it runs.
#guard
  match turnFromCompletionWith kernelTools
      (wrapToolCalls #[("c1", "echo", "{\"text\":\"a\"}"), ("c2", "shell", "{\"cmd\":\"rm\"}")]) with
  | .error (.invalidTag "tool" "name" "shell") => true
  | _ => false

-- Two calls under one id cannot be answered one result each.
#guard
  match turnFromCompletionWith kernelTools
      (wrapToolCalls #[("c1", "echo", "{\"text\":\"a\"}"), ("c1", "echo", "{\"text\":\"b\"}")]) with
  | .error (.illFormed "completion.choices[0].message.tool_calls" "duplicate call id") => true
  | _ => false

-- Anthropic: two `tool_use` blocks are one turn, refused as a single step.
#guard
  let two := wrapAnthropicToolUses #[("t1", "echo", "{\"text\":\"a\"}"), ("t2", "echo", "{\"text\":\"b\"}")]
  (match turnFromCompletionWith kernelTools two Protocol.anthropicMessages with
   | .ok (.invoke #[("t1", .echo "a"), ("t2", .echo "b")]) => true
   | _ => false) &&
  (match stepFromCompletionWith kernelTools two Protocol.anthropicMessages with
   | .error (.illFormed "message.content" "more than one tool call") => true
   | _ => false)

#guard
  match turnFromCompletionWith kernelTools (wrapAnthropicText "done") Protocol.anthropicMessages with
  | .ok (.finish "done") => true
  | _ => false

#guard
  match stepFromCompletionWith kernelTools (wrapAnthropicToolUse "c1" "echo" "{\"text\":\"hi\"}")
      Protocol.anthropicMessages with
  | .ok s => dispatch s == "hi"
  | .error _ => false

#guard
  match stepFromCompletionWith kernelTools (wrapAnthropicToolUse "c3" "shell" "{\"cmd\":\"rm\"}")
      Protocol.anthropicMessages with
  | .error (.invalidTag "tool" "name" "shell") => true
  | _ => false

#guard
  match stepFromCompletionWith kernelTools (wrapAnthropicText "done") Protocol.anthropicMessages with
  | .ok (.finish "done") => true
  | _ => false

end

end LeanAgent
