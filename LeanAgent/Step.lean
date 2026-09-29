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

/-- A decoded model move. Invented tool names never inhabit `invoke`. -/
public inductive ModelStep (Tool : Type := DemoTool) where
  | finish (content : String)
  | invoke (callId : String) (tool : Tool)
  deriving Repr, BEq

public def wrapToolCall (id name argsJson : String) : String :=
  Json.compress (Json.mkObj [
    ("choices", Json.arr #[Json.mkObj [
      ("finish_reason", Json.str "tool_calls"),
      ("message", Json.mkObj [
        ("role", Json.str "assistant"),
        ("content", Json.null),
        ("tool_calls", Json.arr #[Json.mkObj [
          ("id", Json.str id),
          ("type", Json.str "function"),
          ("function", Json.mkObj [
            ("name", Json.str name),
            ("arguments", Json.str argsJson)
          ])
        ]])
      ])
    ]])
  ])

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

public def stepFromAnthropicWith {Tool : Type} (ts : ToolSet Tool) (raw : String) :
    Except DecodeError (ModelStep Tool) := do
  let blocks ← anthropicContentBlocks raw
  let uses :=
    blocks.filter fun b =>
      match b.getObjVal? "type" with
      | .ok t =>
        match t.getStr? with
        | .ok "tool_use" => true
        | _ => false
      | .error _ => false
  match uses[0]? with
  | some call =>
    if uses.size > 1 then
      .error (.illFormed "message.content" "more than one tool call")
    else do
      let (id, name, input) ← decodeAnthropicToolUse call
      let tool ← ts.decode name input
      pure (.invoke id tool)
  | none =>
    let text := joinSep "" (blocks.toList.filterMap anthropicTextOfBlock)
    if nonemptyText text then pure (.finish text)
    else .error (.illFormed "message.content" "blank")

public def stepFromCompletionWith {Tool : Type} (ts : ToolSet Tool) (raw : String)
    (protocol : Protocol := .openAIChat) : Except DecodeError (ModelStep Tool) :=
  match refuseIfTruncated raw protocol with
  | .error e => .error e
  | .ok () =>
    match protocol with
    | .anthropicMessages => stepFromAnthropicWith ts raw
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
        match calls[0]? with
        | some call =>
          if calls.size > 1 then
            .error (.illFormed "completion.choices[0].message.tool_calls" "more than one tool call")
          else do
            let (id, tool) ← decodeFunctionCallWith ts call
            pure (.invoke id tool)
        | none =>
          let content? ← optNullableStrField "completion.choices[0].message" "content" msg
          match content? with
          | some c =>
            if nonemptyText c then pure (.finish c)
            else .error (.illFormed "completion.choices[0].message.content" "blank")
          | none => .error (.illFormed "completion.choices[0].message" "no tool_calls or content")
      | .error _ => do
        let content ← strField "completion.choices[0].message" "content" msg
        if nonemptyText content then pure (.finish content)
        else .error (.illFormed "completion.choices[0].message.content" "blank")

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

#guard
  let two := Json.compress (Json.mkObj [
    ("choices", Json.arr #[Json.mkObj [
      ("finish_reason", Json.str "tool_calls"),
      ("message", Json.mkObj [
        ("role", Json.str "assistant"),
        ("content", Json.null),
        ("tool_calls", Json.arr #[
          Json.mkObj [
            ("id", Json.str "c1"),
            ("type", Json.str "function"),
            ("function", Json.mkObj [
              ("name", Json.str "echo"),
              ("arguments", Json.str "{\"text\":\"a\"}")
            ])
          ],
          Json.mkObj [
            ("id", Json.str "c2"),
            ("type", Json.str "function"),
            ("function", Json.mkObj [
              ("name", Json.str "echo"),
              ("arguments", Json.str "{\"text\":\"b\"}")
            ])
          ]
        ])
      ])
    ]])
  ])
  match stepFromCompletion two with
  | .error (.illFormed "completion.choices[0].message.tool_calls" _) => true
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
