module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Json
public import LeanAgent.ToolSpec
public import LeanAgent.ToolSet
public meta import LeanAgent.Json
public meta import LeanAgent.ToolSpec
public meta import LeanAgent.ToolSet

namespace LeanAgent

open Lean

public section

/-- Closed kernel catalog. A name that is not a constructor cannot inhabit this type. -/
public inductive DemoTool where
  | echo (text : String)
  | arxivSearch (query : String)
  deriving Repr, BEq

public def echoSpec : ToolSpec := {
  name := "echo"
  description := "Return the given text. Lean-authored spec; not an MCP description."
  parameters := objectParams #["text"] [
    ("text", Json.mkObj [("type", Json.str "string")])
  ]
}

public def arxivSearchSpec : ToolSpec := {
  name := "arxiv_search"
  description :=
    "Search arXiv for papers matching a query. Returns ids, titles, and short summaries. " ++
      "Use when the user asks for papers, citations, or related work."
  parameters := objectParams #["query"] [
    ("query", Json.mkObj [("type", Json.str "string")])
  ]
}

public def demoToolSpecs : Array ToolSpec :=
  #[echoSpec, arxivSearchSpec]

public def toolName : DemoTool → String
  | .echo _ => "echo"
  | .arxivSearch _ => "arxiv_search"

public def toolArgumentsJson : DemoTool → Json
  | .echo text => Json.mkObj [("text", Json.str text)]
  | .arxivSearch query => Json.mkObj [("query", Json.str query)]

public def decodeDemoTool (name : String) (args : Json) : Except DecodeError DemoTool :=
  match name with
  | "echo" => do
    let o ← asObj "tool.echo" args
    exactFields "tool.echo" ["text"] o
    let text ← strField "tool.echo" "text" args
    if nonemptyText text then pure (.echo text)
    else .error (.illFormed "tool.echo.text" "blank")
  | "arxiv_search" => do
    let o ← asObj "tool.arxiv_search" args
    exactFields "tool.arxiv_search" ["query"] o
    let q ← strField "tool.arxiv_search" "query" args
    if nonemptyText q then pure (.arxivSearch q)
    else .error (.illFormed "tool.arxiv_search.query" "blank")
  | other => .error (.invalidTag "tool" "name" other)

/-- Tagged encoding for transcripts. OpenAI tool args stay a separate shape. -/
public def encodeDemoTool : DemoTool → Json
  | .echo text => Json.mkObj [("tag", Json.str "echo"), ("text", Json.str text)]
  | .arxivSearch query => Json.mkObj [("tag", Json.str "arxiv_search"), ("query", Json.str query)]

public def decodeTaggedDemoTool (j : Json) : Except DecodeError DemoTool := do
  let ctx := "tool"
  let o ← asObj ctx j
  let tag ← strField ctx "tag" j
  match tag with
  | "echo" =>
    exactFields ctx ["tag", "text"] o
    let text ← strField ctx "text" j
    if nonemptyText text then pure (.echo text)
    else .error (.illFormed "tool.text" "blank")
  | "arxiv_search" =>
    exactFields ctx ["tag", "query"] o
    let q ← strField ctx "query" j
    if nonemptyText q then pure (.arxivSearch q)
    else .error (.illFormed "tool.query" "blank")
  | other => .error (.invalidTag ctx "tag" other)

/-- Pure kernel tools return `some`. `arxiv_search` is an observation, not in this module. -/
public def execute? : DemoTool → Option String
  | .echo text => some text
  | .arxivSearch _ => none

public def execute (t : DemoTool) : String :=
  (execute? t).getD ""

public def kernelTools : ToolSet DemoTool := {
  decode := decodeDemoTool
  decodeTagged := decodeTaggedDemoTool
  encodeTagged := encodeDemoTool
  name := toolName
  argumentsJson := toolArgumentsJson
  specs := demoToolSpecs
  execute? := execute?
}

public def encodeToolCall (callId : String) (tool : DemoTool) : Json :=
  kernelTools.encodeCall callId tool

public def assistantInvokeMessage (callId : String) (tool : DemoTool) : Message :=
  kernelTools.assistantInvokeMessage callId tool

#guard
  match decodeDemoTool "echo" (Json.mkObj [("text", Json.str "hi")]) with
  | .ok t => execute t == "hi"
  | .error _ => false

#guard
  match decodeDemoTool "shell" (Json.mkObj [("cmd", Json.str "rm")]) with
  | .error (.invalidTag "tool" "name" "shell") => true
  | _ => false

#guard
  match decodeDemoTool "arxiv_search" (Json.mkObj [("query", Json.str "lean 4")]) with
  | .ok (.arxivSearch "lean 4") => execute? (.arxivSearch "lean 4") == none
  | _ => false

#guard demoToolSpecs.size == 2
#guard
  (demoToolSpecs.map (·.name)).toList == ["echo", "arxiv_search"]
#guard execute? (.arxivSearch "lean 4") == none
#guard
  match decodeDemoTool "list_catalog" (Json.mkObj []) with
  | .error (.invalidTag "tool" "name" "list_catalog") => true
  | _ => false
#guard
  match decodeDemoTool "show_skillset" (Json.mkObj [("token", Json.str "spec-change")]) with
  | .error (.invalidTag "tool" "name" "show_skillset") => true
  | _ => false
#guard
  match decodeDemoTool "show" (Json.mkObj [("name", Json.str "theme.selection")]) with
  | .error (.invalidTag "tool" "name" "show") => true
  | _ => false
#guard
  match decodeDemoTool "search" (Json.mkObj [("query", Json.str "solution approach")]) with
  | .error (.invalidTag "tool" "name" "search") => true
  | _ => false

end

end LeanAgent
