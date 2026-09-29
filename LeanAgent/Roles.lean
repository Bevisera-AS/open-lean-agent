module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Json
public import LeanAgent.ToolSpec
public import LeanAgent.ToolSet
public import LeanAgent.ToolDSL
public import LeanAgent.Arxiv
public import LeanAgent.WebSearch
public import LeanAgent.Files
public import LeanAgent.Verify
public meta import LeanAgent.Json
public meta import LeanAgent.ToolSpec
public meta import LeanAgent.ToolSet
public meta import LeanAgent.ToolDSL

/-!
Role-specific closed tool catalogs. Each role owns its own closed `Tool`
inductive and a `ToolSet`, so a name outside the role's constructors can never
be invoked. The generic `askWith` loop is reused unchanged: an "agent" is just
`(ToolSet Tool, system prompt, ToolRunner Tool, ProviderConfig)`.
-/

namespace LeanAgent.Roles

open Lean
open LeanAgent

public section

/-! ## Academic researcher: arXiv search only -/

public inductive Academic where
  | arxivSearch (query : String)
  deriving Repr, BEq

public def academicTools : ToolSet Academic := mkToolSet [
  toolDecl1 "arxiv_search"
    "Search arXiv for papers matching a query. Returns ids, titles, and short summaries."
    "query" Academic.arxivSearch (fun | .arxivSearch q => some q)
]

public def academicSpecs : Array ToolSpec := academicTools.specs
public def decodeAcademic : String → Json → Except DecodeError Academic := academicTools.decode

/-! ## Market researcher: web search only -/

public inductive Market where
  | webSearch (query : String)
  deriving Repr, BEq

public def marketTools : ToolSet Market := mkToolSet [
  toolDecl1 "web_search"
    ("Search the web for a query. Returns titles, URLs, and snippets. Use for market " ++
      "size, competitors, pricing, and trends.")
    "query" Market.webSearch (fun | .webSearch q => some q)
]

public def marketSpecs : Array ToolSpec := marketTools.specs
public def decodeMarket : String → Json → Except DecodeError Market := marketTools.decode

/-! ## File reader: read a file / list a directory (no write) -/

public inductive Reader where
  | readFile (path : String)
  | listDir (path : String)
  deriving Repr, BEq

public def readerTools : ToolSet Reader := mkToolSet [
  toolDecl1 "read_file" "Read a UTF-8 text file from the sandbox by relative path."
    "path" Reader.readFile (fun | .readFile p => some p | _ => none),
  toolDecl1 "list_dir" "List entries of a sandbox directory. Use `.` for the sandbox root."
    "path" Reader.listDir (fun | .listDir p => some p | _ => none)
]

public def readerSpecs : Array ToolSpec := readerTools.specs
public def decodeReader : String → Json → Except DecodeError Reader := readerTools.decode

/-! ## File writer: read + write within the sandbox -/

public inductive Writer where
  | readFile (path : String)
  | writeFile (path : String) (content : String)
  deriving Repr, BEq

public def writerTools : ToolSet Writer := mkToolSet [
  toolDecl1 "read_file" "Read a UTF-8 text file from the sandbox by relative path."
    "path" Writer.readFile (fun | .readFile p => some p | _ => none),
  toolDecl2 "write_file"
    "Write UTF-8 text to a sandbox file (creates parent dirs). Relative path only."
    "path" "content" Writer.writeFile (fun | .writeFile p c => some (p, c) | _ => none)
]

public def writerSpecs : Array ToolSpec := writerTools.specs
public def decodeWriter : String → Json → Except DecodeError Writer := writerTools.decode

/-! ## Runners bind each closed tool to its effect. -/

public def academicRunner : ToolRunner Academic := {
  run := fun | .arxivSearch q => Arxiv.search q
}

public def marketRunner : ToolRunner Market := {
  run := fun | .webSearch q => Web.search q
}

public def readerRunner (root : System.FilePath) : ToolRunner Reader := {
  run := fun
    | .readFile p => Files.readFileIn root p
    | .listDir p => Files.listDirIn root p
}

public def writerRunner (root : System.FilePath) : ToolRunner Writer := {
  run := fun
    | .readFile p => Files.readFileIn root p
    | .writeFile p c => Files.writeFileIn root p c
}

/-! ## Verifier: compile Lean snippets (lean/lake as tools) -/

public inductive Verifier where
  | leanCheck (code : String)
  deriving Repr, BEq

public def verifierTools : ToolSet Verifier := mkToolSet [
  toolDecl1 "lean_check"
    ("Compile a self-contained Lean 4 snippet and report whether it elaborates. " ++
      "Returns OK or the compiler diagnostics.")
    "code" Verifier.leanCheck (fun | .leanCheck c => some c)
]

public def verifierSpecs : Array ToolSpec := verifierTools.specs
public def decodeVerifier : String → Json → Except DecodeError Verifier := verifierTools.decode

public def verifierRunner (timeoutSecs : Nat := 30) : ToolRunner Verifier := {
  run := fun
    | .leanCheck code => do
      let v ← Verify.leanCheck code timeoutSecs
      pure v.render
}

/-! Refusal is structural: an off-catalog name cannot inhabit a role's tool. -/

#guard
  match decodeMarket "arxiv_search" (Json.mkObj [("query", Json.str "x")]) with
  | .error (.invalidTag "tool" "name" "arxiv_search") => true
  | _ => false

#guard
  match decodeReader "write_file" (Json.mkObj [("path", Json.str "x"), ("content", Json.str "y")]) with
  | .error (.invalidTag "tool" "name" "write_file") => true
  | _ => false

#guard
  match decodeAcademic "arxiv_search" (Json.mkObj [("query", Json.str "lean 4")]) with
  | .ok (.arxivSearch "lean 4") => true
  | _ => false

#guard
  match decodeWriter "write_file" (Json.mkObj [("path", Json.str "out.txt"), ("content", Json.str "hi")]) with
  | .ok (.writeFile "out.txt" "hi") => true
  | _ => false

#guard
  match decodeVerifier "lean_check" (Json.mkObj [("code", Json.str "#eval 1")]) with
  | .ok (.leanCheck "#eval 1") => true
  | _ => false

#guard
  match decodeVerifier "web_search" (Json.mkObj [("query", Json.str "x")]) with
  | .error (.invalidTag "tool" "name" "web_search") => true
  | _ => false

#guard (readerSpecs.map (·.name)).toList == ["read_file", "list_dir"]
#guard (writerSpecs.map (·.name)).toList == ["read_file", "write_file"]
#guard (verifierSpecs.map (·.name)).toList == ["lean_check"]

end

end LeanAgent.Roles
