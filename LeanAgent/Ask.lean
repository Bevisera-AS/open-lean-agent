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

/-- What a finish gate decides about a finish the model offered, once the kernel's
own checks (non-blank; cited and quoted when `requireCite`) have passed. -/
public inductive FinishVerdict where
  | accept
  /-- Not yet: `detail` goes on the record as a repair event and `reply` is sent to
  the model as the next user message, in the same history. -/
  | nudge (detail : String) (reply : String)
  deriving Repr, BEq

/-- What a finish gate sees: the finish, the run so far, and how many nudges it
has already spent. -/
public structure FinishInfo (Tool : Type := DemoTool) where
  content : String
  /-- The 1-based turn of this finish. -/
  turn : Nat
  /-- Nudges pushed earlier in this run. -/
  nudges : Nat
  /-- Every event recorded before this finish. -/
  events : Array (Event Tool)

public structure AskPolicy (Tool : Type := DemoTool) where
  maxTurns : Nat := 4
  /-- When true, a `finish` is refused unless events include a cite tool plus a
  usable result, and the finish must be `{"quotes":[...]}` copied from that result.
  Only meaningful with a `ToolSet` that marks some tool `isCite`: no catalog in this
  package does (lean-spec's `show` does), so with these catalogs the flag can only
  ever refuse. The repair text therefore names no tool. -/
  requireCite : Bool := false
  /-- Decides a finish that passed the kernel checks: accept it, or nudge the model
  and continue in the same history. `none` accepts every finish. Each nudge spends a
  turn, so `maxTurns` bounds the nudges as well; a nudge on the last turn, a blank
  nudge reply, and a gate that throws are refusals, never a lost transcript. -/
  onFinish : Option (FinishInfo Tool → IO FinishVerdict) := none

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
    else some "finish quotes are not substrings of the cited tool result"

public def renderQuotedFinish (content : String) : String :=
  match decodeQuotedFinish content with
  | .ok qs => joinSep "\n" qs.toList
  | .error _ => content

public def citeRepairMessage : LeanAgent.Message := {
  role := .user
  content :=
    "That answer is not cited. Call one of the offered citation tools, wait for the tool " ++
      "result, then finish with JSON quotes copied from that result. Do not pretend to have " ++
      "called a tool."
}

public def quoteRepairMessage : LeanAgent.Message := {
  role := .user
  content :=
    "That answer is not quoted from the cited tool result. Return only " ++
      "{\"quotes\":[...]} where each string is copied verbatim from that tool output. " ++
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

/-- Bounded tool loop, the only agent loop in the package. Always returns a
receipt. Fatal transport does not retry; retryable 429/5xx retries until
`maxTurns`. Invented tool names refuse the turn. Truncation is a typed stop. A
turn with several tool calls runs them in order: one assistant message carrying
every call, one `invoke`/`result` pair and one tool message per call. A throwing
runner becomes that call's result, not a lost transcript. A finish passes the
kernel checks and then `policy.onFinish`, which may nudge instead. The caller owns
the closed tool set. -/
public def askWith {Tool : Type} (tools : ToolSet Tool) (system : String)
    (c : Completer) (cfg : ProviderConfig) (prompt : String)
    (policy : AskPolicy Tool := {}) (runner : ToolRunner Tool)
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
  -- turns, nudges spent). Outcome: the Transcript.
  let init : Array LeanAgent.Message × Array (Event Tool) × Usage × Nat := (
    #[{ role := .system, content := system }, { role := .user, content := prompt }],
    #[],
    {},
    0
  )
  runBounded policy.maxTurns (init := init)
    (exhausted := fun (_, events, usage, _) =>
      mk (events.push (.repair policy.maxTurns "maxTurns exhausted without a finish"))
        (.refused policy.maxTurns) usage)
    fun turn (msgs, events, usage, nudges) => do
      let refused (events : Array (Event Tool)) (usage : Usage) (detail : String) :=
        pure (f := IO) (.done (mk (events.push (.repair (turn + 1) detail)) (.refused (turn + 1)) usage))
      let body := Json.compress (chatRequestTools cfg msgs tools.specs)
      match ← c.post cfg.chatUrl body with
      | .err e =>
        let events := events.push (.repair (turn + 1) e.detail)
        if shouldRetryPost e turn policy.maxTurns then
          backoff.wait turn
          pure (.more (msgs, events, usage, nudges))
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
          match turnFromCompletionWith tools raw cfg.protocol with
          | .error e => refused events usage e.pretty
          | .ok (.finish content) =>
            if !nonemptyText content then refused events usage "blank finish"
            else
              -- Kernel checks first: a cited, quoted finish when the policy requires one.
              let citeIssue : Option (String × LeanAgent.Message) :=
                if policy.requireCite && !hasCitedShow tools events then
                  some ("finish without a cited tool result", citeRepairMessage)
                else if policy.requireCite then
                  (quotedFinishError tools content events).map (·, quoteRepairMessage)
                else none
              match citeIssue with
              | some (detail, repairMsg) =>
                let events := events.push (.repair (turn + 1) detail)
                if isLastAttempt turn policy.maxTurns then
                  pure (.done (mk events (.refused (turn + 1)) usage))
                else
                  pure (.more (msgs.push { role := .assistant, content } |>.push repairMsg,
                    events, usage, nudges))
              | none =>
                -- Then the caller's gate, if any.
                match policy.onFinish with
                | none => pure (.done (mk (events.push (.finish content)) .finished usage))
                | some gate =>
                  let verdict : Except String FinishVerdict ← try
                      pure (.ok (← gate { content, turn := turn + 1, nudges, events }))
                    catch e => pure (.error s!"finish gate failed: {e}")
                  match verdict with
                  | .error detail => refused events usage detail
                  | .ok .accept => pure (.done (mk (events.push (.finish content)) .finished usage))
                  | .ok (.nudge detail reply) =>
                    if !nonemptyText reply then refused events usage "blank nudge reply"
                    else
                      let events := events.push (.repair (turn + 1) detail)
                      if isLastAttempt turn policy.maxTurns then
                        pure (.done (mk events (.refused (turn + 1)) usage))
                      else
                        pure (.more (msgs.push { role := .assistant, content }
                          |>.push { role := .user, content := reply }, events, usage, nudges + 1))
          | .ok (.invoke calls) =>
            if calls.any (fun (callId, _) => !nonemptyText callId) then
              refused events usage "blank callId"
            else
              -- Every call of the turn, in the model's order, each answered under its
              -- own call id. A runner that throws must not lose the receipt: the
              -- exception becomes that call's result, on the record and visible to
              -- the model, and the loop goes on.
              let mut events := events
              let mut msgs := msgs.push (tools.assistantInvokesMessage calls)
              for (callId, tool) in calls do
                let output ← try runner.run tool catch e =>
                  pure s!"{tools.name tool} error: {e}"
                events := events ++ #[.invoke callId tool, .result callId output]
                msgs := msgs.push (toolResultMessage callId output)
              pure (.more (msgs, events, usage, nudges))

public def ask (c : Completer) (cfg : ProviderConfig) (prompt : String)
    (policy : AskPolicy DemoTool := {}) (runner : ToolRunner DemoTool := ioRunner)
    (runId : String := "") (backoff : BackoffPolicy := {}) : IO (Transcript DemoTool) :=
  askWith kernelTools defaultAskSystem c cfg prompt policy runner runId backoff

public def liveAsk (cfg : ProviderConfig) (prompt : String) (policy : AskPolicy DemoTool := {}) :
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
