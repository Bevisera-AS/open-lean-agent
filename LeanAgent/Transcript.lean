module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Json
public import LeanAgent.Step
public meta import LeanAgent.Json
public meta import LeanAgent.Step

namespace LeanAgent

open Lean

public section

public inductive StopReason where
  | finished
  | refused (attempts : Nat)
  | transport
  | truncated
  deriving Repr, BEq

public inductive RunKind where
  | ask
  | extract
  deriving Repr, BEq, DecidableEq

public def RunKind.toWire : RunKind → String
  | .ask => "ask"
  | .extract => "extract"

public def decodeRunKind (s : String) : Except DecodeError RunKind :=
  match s with
  | "ask" => .ok .ask
  | "extract" => .ok .extract
  | other => .error (.invalidTag "header" "kind" other)

public inductive Event (Tool : Type := DemoTool) where
  | invoke (callId : String) (tool : Tool)
  | result (callId : String) (output : String)
  | repair (attempt : Nat) (detail : String)
  /-- Model chain-of-thought / extended-thinking for one turn. Audit-only: it is
  never treated as output and never re-executed by `replay`. Recorded before the
  turn's `invoke` or `finish`. -/
  | reasoning (turn : Nat) (content : String)
  | finish (content : String)
  deriving Repr, BEq

public def safeRunId (s : String) : Bool :=
  nonemptyText s && s.all fun c => c.isAlphanum || c == '-'

/-- One agent run. Prompt, optional structured output JSON, events, and stop. No secrets. -/
public structure Transcript (Tool : Type := DemoTool) where
  runId : String
  kind : RunKind
  prompt : String
  providerId : String
  model : String
  toolsOffered : Array String
  events : Array (Event Tool)
  outputJson? : Option Json := none
  usage : Usage := {}
  stop : StopReason

public def Transcript.eventsWellFormed {Tool : Type} (events : Array (Event Tool)) : Bool :=
  let rec go (pending : Option String) (finished : Bool) : List (Event Tool) → Bool
    | [] => pending.isNone
    | .invoke callId _tool :: rest =>
      nonemptyText callId && pending.isNone && !finished &&
        go (some callId) false rest
    | .result callId _output :: rest =>
      match pending with
      | some expected =>
        expected == callId && nonemptyText callId && go none false rest
      | none => false
    | .repair _ _ :: rest =>
      pending.isNone && !finished && go none false rest
    | .reasoning _ content :: rest =>
      pending.isNone && !finished && nonemptyText content && go none false rest
    | .finish content :: rest =>
      pending.isNone && !finished && nonemptyText content && rest.isEmpty
  go none false events.toList

public def toolsOfferedCoverInvokesWith {Tool : Type} (ts : ToolSet Tool)
    (t : Transcript Tool) : Bool :=
  t.events.all fun e =>
    match e with
    | .invoke _ tool => t.toolsOffered.contains (ts.name tool)
    | .result _ _ => true
    | .repair _ _ => true
    | .reasoning _ _ => true
    | .finish _ => true

public def Transcript.toolsOfferedCoverInvokes (t : Transcript DemoTool) : Bool :=
  toolsOfferedCoverInvokesWith kernelTools t

public def Transcript.eventsMatchStop {Tool : Type} (t : Transcript Tool) : Bool :=
  match t.stop with
  | .finished =>
    match t.events.back? with
    | some (.finish _) => true
    | _ => false
  | .refused _ =>
    match t.events.back? with
    | some (.finish _) => false
    | some (.invoke _ _) => false
    | some (.result _ _) => false
    | some (.reasoning _ _) => false
    | some (.repair _ _) => true
    | none => false
  | .transport => true
  | .truncated =>
    match t.events.back? with
    | some (.repair _ _) => true
    | _ => false

/-- Metadata plus event state machine: invoke/result call-ids match, at most one
finish, and nothing follows finish. Not a signature or digest. -/
public def wellFormedWith {Tool : Type} (ts : ToolSet Tool) (t : Transcript Tool) : Bool :=
  safeRunId t.runId &&
    nonemptyText t.prompt &&
    nonemptyText t.providerId &&
    nonemptyText t.model &&
    t.toolsOffered.all nonemptyText &&
    t.events.size > 0 &&
    (Transcript.eventsWellFormed t.events) &&
    toolsOfferedCoverInvokesWith ts t &&
    t.eventsMatchStop

public def Transcript.wellFormed (t : Transcript DemoTool) : Bool :=
  wellFormedWith kernelTools t

public def encodeStop : StopReason → Json
  | .finished => Json.mkObj [("tag", Json.str "stop"), ("reason", Json.str "finished")]
  | .refused n => Json.mkObj [
      ("tag", Json.str "stop"),
      ("reason", Json.str "refused"),
      ("attempts", (n : Json))
    ]
  | .transport => Json.mkObj [("tag", Json.str "stop"), ("reason", Json.str "transport")]
  | .truncated => Json.mkObj [("tag", Json.str "stop"), ("reason", Json.str "truncated")]

public def decodeStop (j : Json) : Except DecodeError StopReason := do
  let ctx := "stop"
  let o ← asObj ctx j
  let tag ← strField ctx "tag" j
  if tag != "stop" then
    .error (.invalidTag ctx "tag" tag)
  else do
    let reason ← strField ctx "reason" j
    match reason with
    | "finished" =>
      exactFields ctx ["tag", "reason"] o
      pure .finished
    | "refused" =>
      exactFields ctx ["tag", "reason", "attempts"] o
      let n ← natField ctx "attempts" j
      pure (.refused n)
    | "transport" =>
      exactFields ctx ["tag", "reason"] o
      pure .transport
    | "truncated" =>
      exactFields ctx ["tag", "reason"] o
      pure .truncated
    | other => .error (.invalidTag ctx "reason" other)

public def encodeEventWith {Tool : Type} (ts : ToolSet Tool) : Event Tool → Json
  | .invoke callId tool => Json.mkObj [
      ("tag", Json.str "invoke"),
      ("callId", Json.str callId),
      ("tool", ts.encodeTagged tool)
    ]
  | .result callId output => Json.mkObj [
      ("tag", Json.str "result"),
      ("callId", Json.str callId),
      ("output", Json.str output)
    ]
  | .repair attempt detail => Json.mkObj [
      ("tag", Json.str "repair"),
      ("attempt", (attempt : Json)),
      ("detail", Json.str detail)
    ]
  | .reasoning turn content => Json.mkObj [
      ("tag", Json.str "reasoning"),
      ("turn", (turn : Json)),
      ("content", Json.str content)
    ]
  | .finish content => Json.mkObj [
      ("tag", Json.str "finish"),
      ("content", Json.str content)
    ]

public def encodeEvent : Event DemoTool → Json :=
  encodeEventWith kernelTools

public def decodeEventWith {Tool : Type} (ts : ToolSet Tool) (j : Json) :
    Except DecodeError (Event Tool) := do
  let ctx := "event"
  let o ← asObj ctx j
  let tag ← strField ctx "tag" j
  match tag with
  | "invoke" =>
    exactFields ctx ["tag", "callId", "tool"] o
    let callId ← strField ctx "callId" j
    let tool ← ts.decodeTagged (← field ctx "tool" j)
    pure (.invoke callId tool)
  | "result" =>
    exactFields ctx ["tag", "callId", "output"] o
    let callId ← strField ctx "callId" j
    let output ← strField ctx "output" j
    pure (.result callId output)
  | "repair" =>
    exactFields ctx ["tag", "attempt", "detail"] o
    let attempt ← natField ctx "attempt" j
    let detail ← strField ctx "detail" j
    pure (.repair attempt detail)
  | "reasoning" =>
    exactFields ctx ["tag", "turn", "content"] o
    let turn ← natField ctx "turn" j
    let content ← strField ctx "content" j
    if nonemptyText content then
      pure (.reasoning turn content)
    else
      .error (.illFormed ctx "blank reasoning")
  | "finish" =>
    exactFields ctx ["tag", "content"] o
    let content ← strField ctx "content" j
    pure (.finish content)
  | other => .error (.invalidTag ctx "tag" other)

public def decodeEvent (j : Json) : Except DecodeError (Event DemoTool) :=
  decodeEventWith kernelTools j

public def encodeHeader {Tool : Type} (t : Transcript Tool) : Json :=
  let specField : Json :=
    match t.outputJson? with
    | some j => j
    | none => Json.null
  let natOr (n? : Option Nat) : Json := match n? with | some n => (n : Json) | none => Json.null
  let base := [
    ("tag", Json.str "header"),
    ("runId", Json.str t.runId),
    ("kind", Json.str t.kind.toWire),
    ("prompt", Json.str t.prompt),
    ("providerId", Json.str t.providerId),
    ("model", Json.str t.model),
    ("toolsOffered", Json.arr (t.toolsOffered.map Json.str)),
    ("spec", specField)
  ]
  -- Usage is written only when the provider reported something, keeping headers
  -- for token-less runs (and existing fixtures) unchanged.
  if t.usage.isEmpty then
    Json.mkObj base
  else
    Json.mkObj (base ++ [("usage", Json.mkObj [
      ("promptTokens", natOr t.usage.promptTokens),
      ("completionTokens", natOr t.usage.completionTokens),
      ("totalTokens", natOr t.usage.totalTokens)
    ])])

/-- Read an optional `Nat` from a JSON object field, tolerating null/absence. -/
public def usageNat? (j : Json) (key : String) : Option Nat :=
  match j.getObjVal? key with
  | .error _ => none
  | .ok v => match v.getNat? with | .ok n => some n | .error _ => none

/-- Decode the optional header `usage` object; absent or malformed → empty usage. -/
public def decodeUsage (header : Json) : Usage :=
  match header.getObjVal? "usage" with
  | .error _ => {}
  | .ok u =>
    { promptTokens := usageNat? u "promptTokens"
      completionTokens := usageNat? u "completionTokens"
      totalTokens := usageNat? u "totalTokens" }

public def jsonlLines (s : String) : List String :=
  (s.splitOn "\n").filter nonemptyText

public def encodeJsonlWith {Tool : Type} (ts : ToolSet Tool) (t : Transcript Tool) : String :=
  joinSep "\n"
    (Json.compress (encodeHeader t) ::
      t.events.toList.map (fun e => Json.compress (encodeEventWith ts e)) ++
      [Json.compress (encodeStop t.stop)])

public def encodeJsonl (t : Transcript DemoTool) : String :=
  encodeJsonlWith kernelTools t

public def decodeJsonlWith {Tool : Type} (ts : ToolSet Tool) (s : String) :
    Except DecodeError (Transcript Tool) := do
  let ls := jsonlLines s
  match ls with
  | [] => .error (.illFormed "transcript" "empty")
  | headerLine :: rest =>
    match rest.reverse with
    | [] => .error (.illFormed "transcript" "missing stop")
    | stopLine :: midRev =>
      let header ← parseJson headerLine
      let ho ← asObj "header" header
      exactFields "header"
        ["tag", "runId", "kind", "prompt", "providerId", "model", "toolsOffered", "spec", "usage"] ho
      let htag ← strField "header" "tag" header
      if htag != "header" then
        .error (.invalidTag "header" "tag" htag)
      else do
        let runId ← strField "header" "runId" header
        let kind ← decodeRunKind (← strField "header" "kind" header)
        let prompt ← strField "header" "prompt" header
        let providerId ← strField "header" "providerId" header
        let model ← strField "header" "model" header
        let toolsOffered ← arrStrField "header" "toolsOffered" header
        let specJ ← field "header" "spec" header
        let outputJson? : Option Json :=
          if specJ.isNull then none else some specJ
        let usage := decodeUsage header
        let stopJ ← parseJson stopLine
        let stop ← decodeStop stopJ
        let mid := midRev.reverse
        let events ← mid.toArray.mapM fun line => do
          let j ← parseJson line
          decodeEventWith ts j
        let t : Transcript Tool := {
          runId, kind, prompt, providerId, model, toolsOffered, events, outputJson?, usage, stop
        }
        if wellFormedWith ts t then pure t
        else .error (.illFormed "transcript" "failed wellFormed")

public def decodeJsonl (s : String) : Except DecodeError (Transcript DemoTool) :=
  decodeJsonlWith kernelTools s

/-- Re-execute pure echo. Observations keep recorded output. Does not call a model. -/
public def replayWith {Tool : Type} (ts : ToolSet Tool) (t : Transcript Tool) :
    Except DecodeError String := do
  if !wellFormedWith ts t then
    .error (.illFormed "transcript" "failed wellFormed")
  else
    match t.stop with
    | .transport => .error (.illFormed "transcript" "transport stop cannot replay")
    | .truncated => .error (.illFormed "transcript" "truncated stop cannot replay")
    | .refused n => .error (.illFormed "transcript" s!"refused after {n} attempt(s)")
    | .finished =>
      let rec go (pending : Option (String × Option String)) (last : Option String) :
          List (Event Tool) → Except DecodeError String
        | [] =>
          match last with
          | some s => .ok s
          | none => .error (.illFormed "transcript" "finished without output")
        | .invoke callId tool :: rest =>
          if !nonemptyText callId then
            .error (.illFormed "transcript.invoke" "blank callId")
          else
            go (some (callId, ts.execute? tool)) last rest
        | .result callId output :: rest =>
          match pending with
          | none => .error (.illFormed "transcript.result" "result without invoke")
          | some (pid, expected?) =>
            if pid != callId then
              .error (.illFormed "transcript.result" "callId mismatch")
            else
              match expected? with
              | none =>
                go none (some output) rest
              | some expected =>
                if expected != output then
                  .error (.illFormed "transcript.result" "output does not match execute")
                else
                  go none (some output) rest
        | .repair _attempt _detail :: rest =>
          go pending last rest
        | .reasoning _turn _content :: rest =>
          go pending last rest
        | .finish content :: rest =>
          if nonemptyText content then
            go pending (some content) rest
          else
            .error (.illFormed "transcript.finish" "blank")
      go none none t.events.toList

public def replay (t : Transcript DemoTool) : Except DecodeError String :=
  replayWith kernelTools t

public def receipt (cfg : ProviderConfig) (step : ModelStep DemoTool)
    (prompt : String := "hi") (runId : String := "run-test") : Transcript DemoTool :=
  let offered := demoToolSpecs.map (·.name)
  match step with
  | .finish content => {
      runId
      kind := .ask
      prompt
      providerId := cfg.providerId
      model := cfg.model
      toolsOffered := offered
      events := #[.finish content]
      stop := .finished
    }
  | .invoke callId tool =>
    let output :=
      match execute? tool with
      | some s => if nonemptyText s then s else "ok"
      | none => "ok"
    {
      runId
      kind := .ask
      prompt
      providerId := cfg.providerId
      model := cfg.model
      toolsOffered := offered
      events := #[.invoke callId tool, .result callId output, .finish output]
      stop := .finished
    }

public def defaultAuditDir : System.FilePath := ".lean-agent-audit"

public def auditDirFromEnv : IO System.FilePath := do
  let dir? ← IO.getEnv "LEAN_AGENT_AUDIT_DIR"
  match dir? with
  | some d =>
    if nonemptyText d then pure ⟨d⟩ else pure defaultAuditDir
  | none => pure defaultAuditDir

/-- A run id that resists collisions between runs started in the same
millisecond: monotonic ms plus a random suffix. Stays within `safeRunId`
(alphanumeric + dash), so it is always a safe filename. -/
public def freshRunId : IO String := do
  let ms ← IO.monoMsNow
  -- 8 hex-ish digits of randomness; base 36 would need a table, so keep it decimal.
  let salt ← IO.rand 0 999999999
  pure s!"run-{ms}-{salt}"

/-- Atomic write: render to a sibling `.tmp` file, then rename into place. Avoids
readers ever seeing a partially written transcript. Matches lean-spec's Store.
Crash-between-rename is not a kernel guarantee, but no torn file is observable. -/
public def writeFileAtomic (path : System.FilePath) (contents : String) : IO Unit := do
  let tmp : System.FilePath := ⟨path.toString ++ ".tmp"⟩
  IO.FS.writeFile tmp contents
  IO.FS.rename tmp path

public def writeAuditWith {Tool : Type} (ts : ToolSet Tool) (dir : System.FilePath)
    (t : Transcript Tool) : IO (Except String System.FilePath) := do
  if !wellFormedWith ts t then
    return .error "transcript failed wellFormed"
  if !safeRunId t.runId then
    return .error "runId is not a safe filename"
  IO.FS.createDirAll dir
  let path := dir / (t.runId ++ ".jsonl")
  writeFileAtomic path (encodeJsonlWith ts t)
  return .ok path

public def writeAudit (dir : System.FilePath) (t : Transcript DemoTool) :
    IO (Except String System.FilePath) :=
  writeAuditWith kernelTools dir t

#guard
  match stepFromCompletion (wrapToolCall "c1" "echo" "{\"text\":\"hi\"}") with
  | .ok step =>
    let t := receipt ollama step
    match decodeJsonl (encodeJsonl t) with
    | .ok t2 =>
      match replay t2 with
      | .ok out => out == "hi" && !(encodeJsonl t2).contains "Bearer"
      | .error _ => false
    | .error _ => false
  | .error _ => false

#guard
  let forged := "{\"tag\":\"header\",\"runId\":\"run-x\",\"kind\":\"ask\",\"prompt\":\"p\",\"providerId\":\"ollama\",\"model\":\"x\",\"toolsOffered\":[\"echo\"],\"spec\":null}\n" ++
    "{\"tag\":\"invoke\",\"callId\":\"c\",\"tool\":{\"tag\":\"shell\",\"cmd\":\"rm\"}}\n" ++
    "{\"tag\":\"stop\",\"reason\":\"finished\"}"
  match decodeJsonl forged with
  | .error (.invalidTag "tool" "tag" "shell") => true
  | _ => false

#guard
  let t : Transcript DemoTool := {
    runId := "run-arxiv"
    kind := .ask
    prompt := "find lean 4 papers"
    providerId := "ollama"
    model := "x"
    toolsOffered := #["arxiv_search"]
    events := #[
      .invoke "c1" (.arxivSearch "lean 4"),
      .result "c1" "observed hits",
      .finish "See the hits"
    ]
    stop := .finished
  }
  match replay t with
  | .ok s => s == "See the hits"
  | .error _ => false

-- Reasoning is preserved through JSONL roundtrip, passes wellFormed, and is
-- ignored by replay (audit-only, not output).
#guard
  let t : Transcript DemoTool := {
    runId := "run-reason"
    kind := .ask
    prompt := "find lean 4 papers"
    providerId := "ollama"
    model := "x"
    toolsOffered := #["arxiv_search"]
    events := #[
      .reasoning 1 "I should search arXiv before answering.",
      .invoke "c1" (.arxivSearch "lean 4"),
      .result "c1" "observed hits",
      .reasoning 2 "The hits look relevant; summarize them.",
      .finish "See the hits"
    ]
    stop := .finished
  }
  t.wellFormed &&
    (match decodeJsonl (encodeJsonl t) with
     | .ok t2 =>
       t2.events == t.events &&
         (match replay t2 with
          | .ok s => s == "See the hits"
          | .error _ => false)
     | .error _ => false)

-- A reasoning event with blank content is rejected by wellFormed.
#guard
  let t : Transcript DemoTool := {
    runId := "run-blank-reason"
    kind := .ask
    prompt := "p"
    providerId := "ollama"
    model := "x"
    toolsOffered := #[]
    events := #[.reasoning 1 "   ", .finish "answer"]
    stop := .finished
  }
  !t.wellFormed

#guard
  let bad : Transcript DemoTool := {
    runId := "run-x"
    kind := .ask
    prompt := "p"
    providerId := "ollama"
    model := "x"
    toolsOffered := #["arxiv_search"]
    events := #[
      .invoke "expected" (.arxivSearch "lean 4"),
      .result "different" "hits",
      .finish "nope"
    ]
    stop := .finished
  }
  !bad.wellFormed

end

end LeanAgent
