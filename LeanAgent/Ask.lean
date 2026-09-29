module

public import LeanAgent.Step
public import LeanAgent.Arxiv
public import LeanAgent.Transcript
public import LeanAgent.Live
public import LeanAgent.Json
public import LeanAgent.Retry
public import LeanAgent.Loop
public meta import LeanAgent.Step
public meta import LeanAgent.Loop
public meta import LeanAgent.Arxiv
public meta import LeanAgent.Transcript
public meta import LeanAgent.Live
public meta import LeanAgent.Json

namespace LeanAgent

open Lean
public section

public def defaultAskPrompt : String :=
  "Search arXiv for papers about Lean 4 interactive theorem proving. " ++
    "Cite titles and ids from the tool result. If the tool fails, say so."

public def defaultAskSystem : String :=
  "You are a lean-agent demo. You may call only echo or arxiv_search. " ++
    "When the user asks about papers or related work, call arxiv_search. " ++
    "After you receive a tool result, answer in plain text using that result. " ++
    "Do not invent tool names."

public structure AskPolicy where
  maxTurns : Nat := 4
  /-- When true, a `finish` is refused unless events include a cite tool plus a usable result. -/
  requireCite : Bool := false
  deriving Repr, BEq

/-- Kernel runner: echo is local; arXiv is an observation. -/
public def runTool (t : DemoTool) : IO String :=
  match execute? t with
  | some s => pure s
  | none =>
    match t with
    | .arxivSearch q => Arxiv.search q
    | .echo _ => pure ""

public def ioRunner : ToolRunner DemoTool := { run := runTool }

public def stubArxivRunner (output : String) : ToolRunner DemoTool := {
  run := fun t =>
    match t with
    | .echo text => pure text
    | .arxivSearch _ => pure output
}

public def lastRepairDetail {Tool : Type} (t : Transcript Tool) : Option String :=
  t.events.foldl (init := none) fun acc e =>
    match e with
    | .repair _ d => some d
    | .invoke _ _ => acc
    | .result _ _ => acc
    | .reasoning _ _ => acc
    | .finish _ => acc

public def finishText {Tool : Type} (t : Transcript Tool) : Option String :=
  match t.events.back? with
  | some (.finish c) => some c
  | some (.invoke _ _) => none
  | some (.result _ _) => none
  | some (.repair _ _) => none
  | some (.reasoning _ _) => none
  | none => none

public def citedShowOutputs {Tool : Type} (ts : ToolSet Tool)
    (events : Array (Event Tool)) : Array String :=
  let rec go (waiting : Option String) (acc : Array String) : List (Event Tool) → Array String
    | [] => acc
    | .invoke callId tool :: rest =>
      if ts.isCite tool then go (some callId) acc rest
      else go none acc rest
    | .result callId output :: rest =>
      match waiting with
      | some expected =>
        if expected == callId && ts.usableCite output then
          go none (acc.push output) rest
        else
          go none acc rest
      | none => go none acc rest
    | .repair _ _ :: rest => go waiting acc rest
    | .reasoning _ _ :: rest => go waiting acc rest
    | .finish _ :: rest => go waiting acc rest
  go none #[] events.toList

public def hasCitedShow {Tool : Type} (ts : ToolSet Tool)
    (events : Array (Event Tool)) : Bool :=
  !(citedShowOutputs ts events).isEmpty

public def minQuoteBytes : Nat := 24

public def encodeQuotedFinish (quotes : Array String) : String :=
  Json.compress (Json.mkObj [("quotes", Json.arr (quotes.map Json.str))])

public def decodeQuotedFinish (s : String) : Except DecodeError (Array String) := do
  let j ← parseJson s
  let o ← asObj "finish" j
  exactFields "finish" ["quotes"] o
  let qs ← arrStrField "finish" "quotes" j
  if qs.isEmpty then
    .error (.illFormed "finish.quotes" "empty")
  else if qs.any (fun q => !nonemptyText q) then
    .error (.illFormed "finish.quotes" "blank")
  else if qs.any (fun q => q.utf8ByteSize < minQuoteBytes) then
    .error (.illFormed "finish.quotes" "too short")
  else
    pure qs

public def quotesFromSources (quotes : Array String) (sources : Array String) : Bool :=
  quotes.all fun q => sources.any (fun src => src.contains q)

public def quotedFinishError {Tool : Type} (ts : ToolSet Tool) (content : String)
    (events : Array (Event Tool)) : Option String :=
  match decodeQuotedFinish content with
  | .error e => some e.pretty
  | .ok qs =>
    if quotesFromSources qs (citedShowOutputs ts events) then none
    else some "finish quotes are not substrings of the cited show result"

public def renderQuotedFinish (content : String) : String :=
  match decodeQuotedFinish content with
  | .ok qs => joinSep "\n" qs.toList
  | .error _ => content

public def citeRepairMessage : LeanAgent.Message := {
  role := .user
  content :=
    "That answer is not cited. Call show with a skill id, wait for the tool result, " ++
      "then finish with JSON quotes copied from that result. Do not pretend to have called a tool."
}

public def quoteRepairMessage : LeanAgent.Message := {
  role := .user
  content :=
    "That answer is not quoted from the show result. Return only " ++
      "{\"quotes\":[...]} where each string is copied verbatim from the show tool output. " ++
      "No other fields, no paraphrase."
}

#guard
  match decodeQuotedFinish (encodeQuotedFinish #["Bevisera sits above models; Lean checks stated properties."]) with
  | .ok qs => qs == #["Bevisera sits above models; Lean checks stated properties."]
  | .error _ => false
#guard
  match decodeQuotedFinish "{\"quotes\":[\"too short\"]}" with
  | .error (.illFormed "finish.quotes" "too short") => true
  | _ => false
#guard
  match decodeQuotedFinish "{\"quotes\":[\"long enough to pass the byte floor\"],\"summary\":\"nope\"}" with
  | .error (.unknownFields "finish" ["summary"]) => true
  | _ => false

/-- Bounded tool loop. Always returns a receipt. Fatal transport does not retry;
retryable 429/5xx retries until `maxTurns`. Invented tool names refuse. Truncation
is a typed stop. The caller owns the closed tool set. -/
public def askWith {Tool : Type} (tools : ToolSet Tool) (system : String)
    (c : Completer) (cfg : ProviderConfig) (prompt : String)
    (policy : AskPolicy := {}) (runner : ToolRunner Tool)
    (runId : String := "") (backoff : BackoffPolicy := {}) : IO (Transcript Tool) := do
  let runId ← if safeRunId runId then pure runId else freshRunId
  let offered := tools.specs.map (·.name)
  let mk (events : Array (Event Tool)) (stop : StopReason) (usage : Usage := {}) :
      Transcript Tool := {
    runId
    kind := .ask
    prompt
    providerId := cfg.providerId
    model := cfg.model
    toolsOffered := offered
    events
    usage
    stop
  }
  if policy.maxTurns == 0 then
    return mk #[.repair 0 "maxTurns must be at least 1"] (.refused 0)
  if !nonemptyText prompt then
    return mk #[.repair 0 "blank prompt"] (.refused 0)
  -- State: (message history, accumulated audit events, token usage summed over
  -- turns). Outcome: the Transcript.
  let init : Array LeanAgent.Message × Array (Event Tool) × Usage := (
    #[{ role := .system, content := system }, { role := .user, content := prompt }],
    #[],
    {}
  )
  runBounded policy.maxTurns (init := init)
    (exhausted := fun (_, events, usage) =>
      mk (events.push (.repair policy.maxTurns "maxTurns exhausted without a finish"))
        (.refused policy.maxTurns) usage)
    fun turn (msgs, events, usage) => do
      let body := Json.compress (chatRequestTools cfg msgs tools.specs)
      match ← c.post cfg.chatUrl body with
      | .err e =>
        let events := events.push (.repair (turn + 1) e.detail)
        if shouldRetryPost e turn policy.maxTurns then
          backoff.wait turn
          pure (.more (msgs, events, usage))
        else
          pure (.done (mk events .transport usage))
      | .ok _status raw =>
        if completionTruncated raw cfg.protocol then
          pure (.done (mk (events.push (.repair (turn + 1) "truncated")) .truncated usage))
        else
          -- Accumulate this turn's token usage.
          let usage := usage.add (completionUsage raw cfg.protocol)
          -- Preserve the model's reasoning for this turn before its move. Audit-only:
          -- it is never sent back to the model, never treated as output, and is
          -- ignored by replay.
          let events :=
            match completionReasoning raw cfg.protocol with
            | some r => events.push (.reasoning (turn + 1) r)
            | none => events
          match stepFromCompletionWith tools raw cfg.protocol with
          | .error e =>
            pure (.done (mk (events.push (.repair (turn + 1) e.pretty)) (.refused (turn + 1)) usage))
          | .ok (.finish content) =>
            if !nonemptyText content then
              pure (.done (mk (events.push (.repair (turn + 1) "blank finish"))
                (.refused (turn + 1)) usage))
            else if policy.requireCite && !hasCitedShow tools events then
              let events := events.push (.repair (turn + 1) "finish without cited show result")
              if isLastAttempt turn policy.maxTurns then
                pure (.done (mk events (.refused (turn + 1)) usage))
              else
                pure (.more (msgs.push { role := .assistant, content } |>.push citeRepairMessage,
                  events, usage))
            else if policy.requireCite then
              match quotedFinishError tools content events with
              | some detail =>
                let events := events.push (.repair (turn + 1) detail)
                if isLastAttempt turn policy.maxTurns then
                  pure (.done (mk events (.refused (turn + 1)) usage))
                else
                  pure (.more
                    (msgs.push { role := .assistant, content } |>.push quoteRepairMessage,
                      events, usage))
              | none =>
                pure (.done (mk (events.push (.finish content)) .finished usage))
            else
              pure (.done (mk (events.push (.finish content)) .finished usage))
          | .ok (.invoke callId tool) =>
            if !nonemptyText callId then
              pure (.done (mk (events.push (.repair (turn + 1) "blank callId"))
                (.refused (turn + 1)) usage))
            else
              let output ← runner.run tool
              let events := events ++ #[.invoke callId tool, .result callId output]
              let msgs := msgs.push (tools.assistantInvokeMessage callId tool)
                |>.push (toolResultMessage callId output)
              pure (.more (msgs, events, usage))

public def ask (c : Completer) (cfg : ProviderConfig) (prompt : String)
    (policy : AskPolicy := {}) (runner : ToolRunner DemoTool := ioRunner)
    (runId : String := "") (backoff : BackoffPolicy := {}) : IO (Transcript DemoTool) :=
  askWith kernelTools defaultAskSystem c cfg prompt policy runner runId backoff

public def liveAsk (cfg : ProviderConfig) (prompt : String) (policy : AskPolicy := {}) :
    IO (Transcript DemoTool) :=
  ask (curlCompleter cfg) cfg prompt policy ioRunner

#guard
  let body := Json.compress
    (chatRequestTools ollama #[{ role := .user, content := defaultAskPrompt }] demoToolSpecs)
  body.contains "arxiv_search" &&
    body.contains "echo" &&
    !body.contains "list_catalog" &&
    !body.contains "show_skillset" &&
    body.contains "tool_choice" &&
    body.contains "parallel_tool_calls" &&
    !body.contains "response_format" &&
    !body.contains "shell" &&
    !body.contains "Bearer"

#guard
  let body := Json.compress
    (chatRequestTools anthropic #[{ role := .system, content := defaultAskSystem },
      { role := .user, content := defaultAskPrompt }] demoToolSpecs)
  body.contains "arxiv_search" &&
    body.contains "input_schema" &&
    !body.contains "response_format" &&
    !body.contains "parallel_tool_calls" &&
    !body.contains "\"role\":\"system\"" &&
    body.contains "\"system\""

end

end LeanAgent
