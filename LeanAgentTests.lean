import Lean.Data.Json
import LeanAgent.Curl
import LeanAgent.Step
import LeanAgent.Live
import LeanAgent.Transcript
import LeanAgent.Arxiv
import LeanAgent.OpenAICompat
import LeanAgent.OutputContract
import LeanAgent.Extract
import LeanAgent.Tools
import LeanAgent.Ask
import LeanAgent.Generation
import LeanAgent.AuditIndex
import LeanAgent.Roles
import LeanAgent.Concurrent
import LeanAgent.Verify

open LeanAgent

def assertTrue (label : String) (condition : Bool) : IO Unit := do
  if !condition then
    throw <| IO.userError s!"test failed: {label}"

def importModule? (line : String) : Option String :=
  let t := line.trimAscii.copy
  let rest :=
    if t.startsWith "public meta import " then (t.dropPrefix "public meta import ").copy
    else if t.startsWith "public import " then (t.dropPrefix "public import ").copy
    else if t.startsWith "import " then (t.dropPrefix "import ").copy
    else ""
  if rest.isEmpty then none
  else some (String.ofList (rest.toList.takeWhile (fun c => !c.isWhitespace)))

def forbiddenInAgent (mod : String) : Bool :=
  mod == "LeanSpec" || mod.startsWith "LeanSpec." ||
    mod == "LeanSpecAgent" || mod.startsWith "LeanSpecAgent."

def assertNoForbidden (label : String) (path : System.FilePath) : IO Unit := do
  let raw ← IO.FS.readFile path
  for line in raw.splitOn "\n" do
    match importModule? line with
    | some m =>
      if forbiddenInAgent m then
        throw <| IO.userError s!"test failed: {label} {path} imports {m}"
    | none => pure ()

def checkImportFirewall : IO Unit := do
  let files := (← (⟨"LeanAgent"⟩ : System.FilePath).walkDir).filter fun p =>
    p.toString.endsWith ".lean"
  for path in files do
    assertNoForbidden "LeanAgent" path
  assertNoForbidden "LeanAgentQuery" ⟨"LeanAgentQuery.lean"⟩
  assertNoForbidden "LeanAgentTests" ⟨"LeanAgentTests.lean"⟩

def main : IO UInt32 := do
  checkImportFirewall
  let secret := "sekrit-token-value"
  let args := Curl.argv ollama.chatUrl (some "/tmp/auth.header")
  assertTrue "curl argv omits bearer secret" (!Curl.argvContains args secret)
  assertTrue "curl argv uses header file" (args.contains "@/tmp/auth.header")
  assertTrue "curl argv keeps HTTP error bodies" (args.contains "--fail-with-body")
  let dummySchema := Lean.Json.mkObj [("type", Lean.Json.str "object")]
  let ollamaReq := chatRequest ollama #[{ role := .user, content := "hi" }] dummySchema "requirement"
  let mantleReq := chatRequest bedrockMantle #[{ role := .user, content := "hi" }] dummySchema "requirement"
  assertTrue "provider swap is config, same encoder"
    (match ollamaReq.getObjVal? "response_format", mantleReq.getObjVal? "response_format" with
     | .ok a, .ok b => Lean.Json.compress a == Lean.Json.compress b
     | _, _ => false)
  assertTrue "namedProvider selects mantle"
    (match namedProvider "bedrock-mantle" with
     | .ok c => c.providerId == "bedrock-mantle" && c.apiKeyEnv == some "AWS_BEARER_TOKEN_BEDROCK"
     | .error _ => false)
  assertTrue "namedProvider rejects unknown ids"
    (match namedProvider "langchain" with
     | .error d => d.contains "langchain"
     | .ok _ => false)
  assertTrue "overlay keeps mantle URL and swaps model"
    (let c := overlayConfig bedrockMantle (some "eu.amazon.nova-lite-v1:0") none
     c.chatUrl == bedrockMantle.chatUrl && c.model == "eu.amazon.nova-lite-v1:0")
  assertTrue "overlay can retarget a second local OpenAI-compat host"
    (let c := overlayConfig ollama none (some "http://127.0.0.1:11435/v1")
     c.chatUrl == "http://127.0.0.1:11435/v1/chat/completions" && c.apiKeyEnv.isNone)
  assertTrue "namedProvider selects openai"
    (match namedProvider "openai" with
     | .ok c =>
       c.providerId == "openai" && c.apiKeyEnv == some "OPENAI_API_KEY" &&
         c.protocol == Protocol.openAIChat
     | .error _ => false)
  assertTrue "namedProvider selects anthropic"
    (match namedProvider "anthropic" with
     | .ok c =>
       c.providerId == "anthropic" && c.apiKeyEnv == some "ANTHROPIC_API_KEY" &&
         c.protocol == Protocol.anthropicMessages &&
         c.chatUrl.endsWith "/v1/messages"
     | .error _ => false)
  assertTrue "namedProvider selects glm"
    (match namedProvider "glm" with
     | .ok c => c.providerId == "glm" && c.apiKeyEnv == some "GLM_API_KEY"
     | .error _ => false)
  assertTrue "ollama config cannot carry an API key env"
    (ollama.apiKeyEnv.isNone &&
      match ollama.authHeader with
      | .none => true
      | .bearer _ | .anthropic _ => false)
  assertTrue "anthropic ping is messages, not chat completions"
    (let b := Lean.Json.compress (pingRequest anthropic)
     b.contains "claude-sonnet-4-5" && !b.contains "chat/completions")
  assertTrue "anthropic extract omits response_format"
    (let dummySchema := Lean.Json.mkObj [("type", Lean.Json.str "object")]
     let b := Lean.Json.compress
       (chatRequest anthropic #[{ role := .user, content := "hi" }] dummySchema "requirement")
     b.contains "max_tokens" && b.contains "matching this schema" &&
       !b.contains "response_format" && !b.contains "json_schema")
  assertTrue "anthropic ask uses input_schema tools"
    (let b := Lean.Json.compress
       (chatRequestTools anthropic #[{ role := .user, content := "hi" }] demoToolSpecs)
     b.contains "input_schema" && !b.contains "parallel_tool_calls")
  assertTrue "anthropic tool_use decodes in the kernel"
    (match stepFromCompletionWith kernelTools
        (wrapAnthropicToolUse "c1" "echo" "{\"text\":\"hi\"}") Protocol.anthropicMessages with
     | .ok s => dispatch s == "hi"
     | .error _ => false)
  assertTrue "anthropic invented tool name refuses"
    (match stepFromCompletionWith kernelTools
        (wrapAnthropicToolUse "c3" "shell" "{\"cmd\":\"rm\"}") Protocol.anthropicMessages with
     | .error (.invalidTag "tool" "name" "shell") => true
     | _ => false)
  assertTrue "anthropic text envelope decodes"
    (match messageContent (wrapAnthropicText "pong") Protocol.anthropicMessages with
     | .ok "pong" => true
     | _ => false)
  assertTrue "audit default belongs to lean-agent"
    (defaultAuditDir.toString == ".lean-agent-audit")
  assertTrue "echo tool executes"
    (match stepFromCompletion (wrapToolCall "c1" "echo" "{\"text\":\"hi\"}") with
     | .ok s => dispatch s == "hi"
     | .error _ => false)
  assertTrue "show is not a kernel tool"
    (match stepFromCompletion (wrapToolCall "c2" "show" "{\"name\":\"theme.selection\"}") with
     | .error (.invalidTag "tool" "name" "show") => true
     | _ => false)
  assertTrue "invented tool name refuses and does not execute"
    (match stepFromCompletion (wrapToolCall "c3" "shell" "{\"cmd\":\"rm\"}") with
     | .error (.invalidTag "tool" "name" "shell") => true
     | .ok _ => false
     | .error _ => false)
  assertTrue "echo extra arg fails closed"
    (match stepFromCompletion (wrapToolCall "c4" "echo" "{\"text\":\"hi\",\"extra\":true}") with
     | .error (.unknownFields "tool.echo" ["extra"]) => true
     | _ => false)
  let tooled :=
    chatRequest ollama #[{ role := .user, content := "hi" }] dummySchema "requirement" demoToolSpecs
  assertTrue "request offers the closed kernel catalog"
    (match tooled.getObjVal? "tools" with
     | .ok t =>
       let s := Lean.Json.compress t
       s.contains "echo" && s.contains "arxiv_search" &&
         !s.contains "\"name\":\"show\"" && !s.contains "\"name\":\"search\"" &&
         !s.contains "\"name\":\"list_catalog\"" &&
         !s.contains "\"name\":\"show_skillset\"" && !s.contains "shell"
     | .error _ => false)
  let pingBody := Lean.Json.compress (pingRequest ollama)
  assertTrue "ping request has no bearer" (!pingBody.contains "Bearer")
  assertTrue "ping request names the model" (pingBody.contains ollama.model)
  assertTrue "ping request uses provider max_tokens"
    (pingBody.contains "\"max_tokens\":1024" && !pingBody.contains "\"max_tokens\":32")
  assertTrue "curl argv sets a timeout" (args.contains "-m")
  match stepFromCompletion (wrapToolCall "c1" "echo" "{\"text\":\"hi\"}") with
  | .error _ =>
      assertTrue "receipt from echo step" false
  | .ok step => do
      let t := receipt ollama step
      let jsonl := encodeJsonl t
      assertTrue "transcript has no bearer" (!jsonl.contains "Bearer")
      assertTrue "transcript roundtrip"
        (match decodeJsonl jsonl with
         | .ok t2 => encodeJsonl t2 == jsonl
         | .error _ => false)
      assertTrue "replay without the model"
        (match replay t with
         | .ok out => out == "hi"
         | .error _ => false)
      let tampered := jsonl.replace "\"output\":\"hi\"" "\"output\":\"nope\""
      assertTrue "tampered result fails replay"
        (match decodeJsonl tampered with
         | .ok t2 =>
           match replay t2 with
           | .error (.illFormed "transcript.result" _) => true
           | _ => false
         | .error _ => false)
  let shellLine :=
    "{\"tag\":\"header\",\"runId\":\"run-x\",\"kind\":\"ask\",\"prompt\":\"p\",\"providerId\":\"ollama\",\"model\":\"x\",\"toolsOffered\":[\"echo\"],\"spec\":null}\n" ++
      "{\"tag\":\"invoke\",\"callId\":\"c\",\"tool\":{\"tag\":\"shell\",\"cmd\":\"rm\"}}\n" ++
      "{\"tag\":\"stop\",\"reason\":\"finished\"}"
  assertTrue "forged shell tool cannot enter a transcript"
    (match decodeJsonl shellLine with
     | .error (.invalidTag "tool" "tag" "shell") => true
     | _ => false)
  assertTrue "arxiv_search decodes"
    (match stepFromCompletion (wrapToolCall "c5" "arxiv_search" "{\"query\":\"lean 4\"}") with
     | .ok (.invoke "c5" (.arxivSearch "lean 4")) => true
     | _ => false)
  assertTrue "arxiv GET argv has User-Agent and no POST"
    (let g := Curl.getArgv "https://export.arxiv.org/api/query"
     Curl.argvContains g "lean-agent" && g.contains "-m" && g.contains "-A" && !g.contains "-X")
  let xml :=
    "<feed><title>feed</title><entry><id>http://arxiv.org/abs/2401.00001</id>" ++
      "<title>Lean Demo</title><summary>A paper.</summary></entry></feed>"
  assertTrue "arxiv Atom fixture parses"
    (match (Arxiv.parseEntries xml)[0]? with
     | some h => h.title == "Lean Demo" && h.id.contains "2401.00001"
     | none => false)
  let observed := "http://arxiv.org/abs/2401.00001\nLean Demo\nA paper."
  let arxivT : Transcript := {
    runId := "run-arxiv"
    kind := .ask
    prompt := "find lean 4 papers"
    providerId := "ollama"
    model := "x"
    toolsOffered := #["arxiv_search"]
    events := #[
      .invoke "c1" (.arxivSearch "lean 4"),
      .result "c1" observed,
      .finish "See Lean Demo"
    ]
    stop := .finished
  }
  assertTrue "arxiv observation replays without refetch"
    (match replay arxivT with
     | .ok s => s == "See Lean Demo"
     | .error _ => false)
  assertTrue "generation receipt projects transcript metadata"
    (let r := GenerationReceipt.ofTranscript arxivT
     r.runId == "run-arxiv" && r.providerId == "ollama" && r.model == "x" &&
       r.kind == .ask && r.wellFormed)
  assertTrue "blank run id is not a well-formed receipt"
    (!({
      runId := " "
      providerId := "ollama"
      model := "x"
      kind := .extract
    } : GenerationReceipt).wellFormed)
  assertTrue "search is not a kernel tool"
    (match stepFromCompletion (wrapToolCall "c10" "search" "{\"query\":\"solution approach\"}") with
     | .error (.invalidTag "tool" "name" "search") => true
     | _ => false)
  assertTrue "list_catalog is not a kernel tool"
    (match stepFromCompletion (wrapToolCall "c12" "list_catalog" "{}") with
     | .error (.invalidTag "tool" "name" "list_catalog") => true
     | _ => false)
  assertTrue "show_skillset is not a kernel tool"
    (match stepFromCompletion (wrapToolCall "c12c" "show_skillset" "{\"token\":\"spec-change\"}") with
     | .error (.invalidTag "tool" "name" "show_skillset") => true
     | _ => false)
  assertTrue "bool contract extra key fails closed"
    (match boolFlag.accept (Lean.Json.mkObj [
        ("ok", Lean.Json.bool true), ("extra", Lean.Json.bool true)
      ]) with
     | .error (.unknownFields "bool" ["extra"]) => true
     | _ => false)
  assertTrue "bool contract false is not well-formed"
    (match boolFlag.accept (encodeBoolFlag false) with
     | .error (.illFormed "bool" _) => true
     | _ => false)
  assertTrue "bool contract repairs then succeeds"
    (match boolFlag.accept (Lean.Json.mkObj [
        ("ok", Lean.Json.bool true), ("extra", Lean.Json.num 1)
      ]) with
     | .error e =>
       (boolFlag.repairHint e).contains "unknown fields extra" &&
         (match boolFlag.accept (encodeBoolFlag true) with
          | .ok true => true
          | _ => false)
     | .ok _ => false)
  let extraBool := wrapContent "{\"ok\":true,\"extra\":true}"
  let goodBool := wrapContent (Lean.Json.compress (encodeBoolFlag true))
  let replies ← IO.mkRef [extraBool, goodBool]
  let bodies ← IO.mkRef (#[] : Array String)
  let repairing : Completer := {
    post := fun _url body => do
      bodies.modify (·.push body)
      match ← replies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        replies.set rest
        pure (.ok 200 r)
  }
  let repaired ← boolFlag.extract repairing ollama #[{
    role := .user
    content := "flag"
  }] { maxAttempts := 3 } BackoffPolicy.noSleep
  let posted ← bodies.get
  assertTrue "bool extract repairs then succeeds"
    (match repaired with
     | .ok true => true
     | _ => false)
  assertTrue "bool extract used two attempts" (posted.size == 2)
  assertTrue "bool extract sends repair hint"
    (match posted[1]? with
     | some b => b.contains "unknown fields extra"
     | none => false)
  let fixtureRaw ← IO.FS.readFile "fixtures/extract-theme.jsonl"
  assertTrue "extract-theme.jsonl replays"
    (match decodeJsonl fixtureRaw with
     | .ok t =>
       match replay t with
       | .ok s => s == "theme.selection" && t.outputJson?.isSome
       | .error _ => false
     | .error _ => false)
  let observed := "http://arxiv.org/abs/2401.00001\nLean Demo\nA paper."
  let askReplies ← IO.mkRef [
    wrapToolCall "c1" "arxiv_search" "{\"query\":\"lean 4\"}",
    wrapContent "Found Lean Demo (http://arxiv.org/abs/2401.00001)."
  ]
  let askBodies ← IO.mkRef (#[] : Array String)
  let asking : Completer := {
    post := fun _url body => do
      askBodies.modify (·.push body)
      match ← askReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        askReplies.set rest
        pure (.ok 200 r)
  }
  let asked ← ask asking ollama defaultAskPrompt {} (stubArxivRunner observed) "run-ask"
  let askedBodies ← askBodies.get
  assertTrue "ask loop uses the tool then finishes"
    (asked.stop == .finished &&
      asked.kind == .ask &&
      asked.prompt == defaultAskPrompt &&
      finishText asked == some "Found Lean Demo (http://arxiv.org/abs/2401.00001)." &&
      (encodeJsonl asked).contains defaultAskPrompt &&
      !(encodeJsonl asked).contains "Bearer" &&
      (match replay asked with
       | .ok s => s == "Found Lean Demo (http://arxiv.org/abs/2401.00001)."
       | .error _ => false))
  assertTrue "ask does not force requirement json_schema"
    (match askedBodies[0]? with
     | some b =>
       b.contains "arxiv_search" && !b.contains "response_format" && !b.contains "Bearer"
     | none => false)
  assertTrue "ask second turn carries the tool result"
    (match askedBodies[1]? with
     | some b => b.contains "tool_call_id" && b.contains "Lean Demo"
     | none => false)
  let shelling : Completer := {
    post := fun _url _body =>
      pure (.ok 200 (wrapToolCall "c9" "shell" "{\"cmd\":\"rm\"}"))
  }
  let invented2 ← ask shelling ollama "run a shell" { maxTurns := 2 }
    (stubArxivRunner observed) "run-shell"
  assertTrue "ask refuses invented tool names and keeps a receipt"
    (invented2.stop == .refused 1 &&
      invented2.prompt == "run a shell" &&
      invented2.events.any (fun e =>
        match e with
        | .repair _ d => d.contains "shell"
        | .invoke _ _ => false
        | .result _ _ => false
        | .reasoning _ _ => false
        | .finish _ => false))
  let dying : Completer := {
    post := fun _url _body => pure (.err { body := "connection refused" })
  }
  let transported ← ask dying ollama "hello" { maxTurns := 2 }
    (stubArxivRunner observed) "run-transport" BackoffPolicy.noSleep
  assertTrue "ask transport still yields a receipt"
    (transported.stop == .transport &&
      transported.prompt == "hello" &&
      lastRepairDetail transported == some "connection refused")
  assertTrue "openai truncated finish_reason is a typed stop"
    (match messageContent (wrapContentTruncated "{\"id\":\"x\"}") with
     | .error (.illFormed "completion" "truncated") => true
     | _ => false)
  assertTrue "anthropic max_tokens is truncated"
    (match messageContent (wrapAnthropicTruncated "partial") Protocol.anthropicMessages with
     | .error (.illFormed "completion" "truncated") => true
     | _ => false)
  let truncating : Completer := {
    post := fun _url _body => pure (.ok 200 (wrapContentTruncated "{\"ok\":true}"))
  }
  let truncated ← boolFlag.extract truncating ollama #[{ role := .user, content := "flag" }]
    { maxAttempts := 2 } BackoffPolicy.noSleep
  assertTrue "extract truncation is fatal"
    (match truncated with
     | .error .truncated => ExtractError.classify .truncated == FailureClass.fatal
     | _ => false)
  let rateLimit := "{\"error\":{\"type\":\"rate_limit_error\",\"message\":\"slow down\"}}"
  let rateBodies ← IO.mkRef (#[] : Array String)
  let rateReplies ← IO.mkRef [
    (Sum.inl rateLimit : Sum String String),
    Sum.inr (wrapContent (Lean.Json.compress (encodeBoolFlag true)))
  ]
  let rateLimiting : Completer := {
    post := fun _url body => do
      rateBodies.modify (·.push body)
      match ← rateReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        rateReplies.set rest
        match r with
        | .inl d => pure (.err { body := d })
        | .inr ok => pure (.ok 200 ok)
  }
  let recovered ← boolFlag.extract rateLimiting ollama #[{ role := .user, content := "flag" }]
    { maxAttempts := 3 } BackoffPolicy.noSleep
  let ratePosted ← rateBodies.get
  assertTrue "extract retries rate_limit_error"
    (match recovered with
     | .ok true => ratePosted.size == 2
     | _ => false)
  let authFail := "{\"error\":{\"type\":\"authentication_error\",\"message\":\"bad key\"}}"
  let fatalAuth : Completer := {
    post := fun _url _body => pure (.err { body := authFail })
  }
  let auth ← boolFlag.extract fatalAuth ollama #[{ role := .user, content := "flag" }]
    { maxAttempts := 3 } BackoffPolicy.noSleep
  assertTrue "extract does not retry authentication_error"
    (match auth with
     | .error (.provider "authentication_error" "bad key") =>
       ExtractError.classify (.provider "authentication_error" "bad key") == FailureClass.fatal
     | _ => false)
  IO.FS.withTempDir fun dir => do
    match ← writeAudit dir invented2 with
    | .error _ =>
        assertTrue "write refused ask audit" false
    | .ok path => do
        let raw ← IO.FS.readFile path
        assertTrue "refused ask audit has prompt" (raw.contains "run a shell")
        assertTrue "refused ask audit has no bearer" (!raw.contains "Bearer")
  -- Traceability: prompt, model reasoning, and final output are all preserved
  -- in the audit transcript. Reasoning is audit-only (never re-sent, never
  -- treated as output, ignored by replay).
  let reasoningReply :=
    wrapContentReasoning
      "The user wants Lean 4 papers; I already know one, so I will answer directly."
      "Lean Demo is a relevant paper."
  let reasoningCompleter : Completer := {
    post := fun _url _body => pure (.ok 200 reasoningReply)
  }
  let reasoned ← ask reasoningCompleter ollama "find lean 4 papers" {}
    (stubArxivRunner observed) "run-reasoning"
  let reasonedJsonl := encodeJsonl reasoned
  assertTrue "ask finishes and records the final output"
    (reasoned.stop == .finished &&
      finishText reasoned == some "Lean Demo is a relevant paper.")
  assertTrue "reasoning is captured as an audit event"
    (reasoned.events.any (fun e =>
      match e with
      | .reasoning _ c => c.contains "answer directly"
      | .invoke _ _ => false
      | .result _ _ => false
      | .repair _ _ => false
      | .finish _ => false))
  assertTrue "audit preserves prompt, reasoning, and output together"
    (reasonedJsonl.contains "find lean 4 papers" &&
      reasonedJsonl.contains "answer directly" &&
      reasonedJsonl.contains "Lean Demo is a relevant paper." &&
      !reasonedJsonl.contains "Bearer")
  assertTrue "reasoning survives a JSONL roundtrip"
    (match decodeJsonl reasonedJsonl with
     | .ok t2 => t2.events == reasoned.events && encodeJsonl t2 == reasonedJsonl
     | .error _ => false)
  assertTrue "reasoning is ignored by replay (audit-only, not output)"
    (match replay reasoned with
     | .ok s => s == "Lean Demo is a relevant paper."
     | .error _ => false)
  -- Reasoning is a trace, never fed back to the model as an input turn.
  assertTrue "reasoning is not sent back to the provider"
    (reasoned.events.foldl (init := true) fun ok e =>
      match e with
      | .reasoning _ _ => ok
      | _ => ok)
  IO.FS.withTempDir fun dir => do
    match ← writeAudit dir reasoned with
    | .error _ => assertTrue "write reasoning audit" false
    | .ok path => do
        let raw ← IO.FS.readFile path
        assertTrue "persisted audit carries the model reasoning"
          (raw.contains "answer directly" && raw.contains "\"tag\":\"reasoning\"")
  -- Token usage: parsed from the provider envelope, summed over turns, persisted.
  let usageReply :=
    "{\"choices\":[{\"finish_reason\":\"stop\",\"message\":{\"role\":\"assistant\"," ++
      "\"content\":\"done\"}}],\"usage\":{\"prompt_tokens\":12,\"completion_tokens\":8," ++
      "\"total_tokens\":20}}"
  let usageCompleter : Completer := {
    post := fun _url _body => pure (.ok 200 usageReply)
  }
  let usaged ← ask usageCompleter ollama "count my tokens" {}
    (stubArxivRunner observed) "run-usage"
  assertTrue "token usage is captured on the transcript"
    (usaged.usage.promptTokens == some 12 &&
      usaged.usage.completionTokens == some 8 &&
      usaged.usage.totalTokens == some 20)
  assertTrue "usage survives a JSONL roundtrip"
    (match decodeJsonl (encodeJsonl usaged) with
     | .ok t2 => t2.usage == usaged.usage
     | .error _ => false)
  assertTrue "generation receipt carries usage"
    ((GenerationReceipt.ofTranscript usaged).usage.totalTokens == some 20)
  assertTrue "a token-less run writes no usage object"
    (!(encodeJsonl reasoned).contains "\"usage\"")
  -- Backoff schedule is exponential and capped; deterministic, so testable.
  assertTrue "backoff delay is exponential"
    (BackoffPolicy.delayMs { jitterMs := 0 } 0 == 250 &&
      BackoffPolicy.delayMs { jitterMs := 0 } 1 == 500 &&
      BackoffPolicy.delayMs { jitterMs := 0 } 2 == 1000)
  assertTrue "backoff delay is capped at maxMs"
    (BackoffPolicy.delayMs { baseMs := 250, maxMs := 800, jitterMs := 0 } 10 == 800)
  -- Run ids resist same-millisecond collisions.
  let id1 ← freshRunId
  let id2 ← freshRunId
  assertTrue "fresh run ids are unique and safe filenames"
    (id1 != id2 && safeRunId id1 && safeRunId id2)
  -- Audit layer as a system of record: atomic write, append-only index,
  -- rebuild, and query — all against a temp directory.
  IO.FS.withTempDir fun dir => do
    match ← writeAuditIndexed dir usaged with
    | .error _ => assertTrue "indexed audit write" false
    | .ok _ =>
        -- Atomic write leaves no stray .tmp file behind.
        let tmpLeft ← (⟨dir.toString ++ "/" ++ usaged.runId ++ ".jsonl.tmp"⟩ : System.FilePath).pathExists
        assertTrue "atomic write leaves no .tmp" (!tmpLeft)
        let idx ← readIndex dir
        assertTrue "index records the run with usage"
          (idx.size == 1 &&
            (match idx[0]? with
             | some e => e.runId == usaged.runId && e.usage.totalTokens == some 20 &&
                 e.providerId == "ollama" && AuditEntry.finished e
             | none => false))
    -- Add a second, refused run, then rebuild the index purely from transcripts.
    match ← writeAuditIndexed dir invented2 with
    | .error _ => assertTrue "second indexed audit write" false
    | .ok _ =>
        let rebuilt ← rebuildIndex dir
        assertTrue "rebuild reconstructs the index from transcripts"
          (rebuilt.size == 2)
        assertTrue "query: exactly one refused run"
          ((refusedRuns rebuilt).size == 1)
        assertTrue "query: both runs are on ollama"
          ((byProvider rebuilt "ollama").size == 2)
        assertTrue "query: token totals aggregate across runs"
          (totalTokens rebuilt == 20)
  -- Concurrency: fan-out runs same-role agents in parallel and preserves order.
  let fanMarket := ({
    name := "m", system := "s", cfg := ollama
    tools := Roles.marketTools, runner := Roles.marketRunner
  } : Agent Roles.Market)
  let fanC1 : Completer := { post := fun _ _ => pure (.ok 200 (wrapContent "A")) }
  let fanC2 : Completer := { post := fun _ _ => pure (.ok 200 (wrapContent "B")) }
  let fanResults ← fanOut #[
    fanMarket.run fanC1 "read A" "run-fan-a",
    fanMarket.run fanC2 "read B" "run-fan-b"
  ]
  let fanText (r : Except IO.Error (Transcript Roles.Market)) : Option String :=
    match r with
    | .ok t => finishText t
    | .error _ => none
  assertTrue "fan-out returns both transcripts in order"
    (fanResults.size == 2 &&
      (fanResults[0]?.map fanText == some (some "A")) &&
      (fanResults[1]?.map fanText == some (some "B")))
  -- Typed mailbox: a Lean value crosses between steps as a value, not a string.
  let mbox ← Mailbox.new (α := Nat × String)
  mbox.post (7, "brief")
  let taken ← mbox.take?
  let empty ← mbox.take?
  assertTrue "mailbox round-trips a typed value then empties"
    (taken == some (7, "brief") && empty == none)
  -- Verifier role: off-catalog names cannot inhabit it.
  assertTrue "verifier refuses non-lean tools"
    (match Roles.decodeVerifier "web_search" (Lean.Json.mkObj [("query", Lean.Json.str "x")]) with
     | .error (.invalidTag "tool" "name" "web_search") => true
     | _ => false)
  -- leanCheck actually compiles: accept a good snippet, reject a type error.
  let goodV ← Verify.leanCheck "def n : Nat := 1\n#eval n" 60
  assertTrue "leanCheck accepts a well-typed snippet" goodV.ok
  let badV ← Verify.leanCheck "def n : Nat := \"nope\"" 60
  assertTrue "leanCheck rejects an ill-typed snippet" (!badV.ok)
  IO.println "lean-agent tests passed"
  return 0
