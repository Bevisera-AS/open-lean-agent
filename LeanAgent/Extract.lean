module

public import Lean.Data.Json
public import LeanAgent.OutputContract
public import LeanAgent.OpenAICompat
public import LeanAgent.Retry
public import LeanAgent.Loop
public import LeanAgent.Completer
public import LeanAgent.Transcript
public import LeanAgent.Util
public meta import LeanAgent.OutputContract
public meta import LeanAgent.OpenAICompat
public meta import LeanAgent.Retry
public meta import LeanAgent.Loop
public meta import LeanAgent.Transcript

namespace LeanAgent

open Lean

public section

public def acceptFromCompletion {α : Type} (contract : OutputContract α) (raw : String)
    (protocol : Protocol := .openAIChat) : Except DecodeError α := do
  let content ← messageContent raw protocol
  let j ← parseJson content
  contract.accept j

/-- Instructor-shaped extract: JSON on the wire, `α` as the accept type.

Decode failures are sent back via `repairHint` until `maxAttempts`.
The bound refuses; it never returns a partial value. Truncation is fatal.
Retryable provider failures (429/5xx/rate-limit) retry; other transport is fatal. -/
public def OutputContract.extract {α : Type} (contract : OutputContract α) (c : Completer)
    (cfg : ProviderConfig) (msgs : Array Message) (policy : ExtractPolicy := {})
    (backoff : BackoffPolicy := {}) :
    IO (Except ExtractError α) := do
  if policy.maxAttempts == 0 then
    return .error (.refused (.illFormed "extract" "maxAttempts must be at least 1") 0)
  -- State: the message history. Outcome: `Except ExtractError α`.
  runBounded policy.maxAttempts (init := msgs)
    (exhausted := fun _ => .error (.refused (.illFormed "extract" "no attempt ran") 0))
    fun attempt msgs => do
      let body := Json.compress (chatRequest cfg msgs contract.schema contract.name)
      match ← c.post cfg.chatUrl body with
      | .err e =>
        if shouldRetryPost e attempt policy.maxAttempts then
          backoff.wait attempt
          pure (.more (appendRepair msgs none e.detail))
        else
          match e.provider? with
          | some (code, msg) => pure (.done (.error (.provider code msg)))
          | none => pure (.done (.error (.transport e.detail)))
      | .ok _status raw =>
        if completionTruncated raw cfg.protocol then
          pure (.done (.error .truncated))
        else
          match acceptFromCompletion contract raw cfg.protocol with
          | .ok a => pure (.done (.ok a))
          | .error e =>
            if isLastAttempt attempt policy.maxAttempts then
              pure (.done (.error (.refused e policy.maxAttempts)))
            else
              let content? :=
                match messageContent raw cfg.protocol with
                | .ok content => some content
                | .error _ => none
              pure (.more (appendRepair msgs content? (contract.repairHint e)))

/-- Same accept loop, with a receipt. On success `outputJson?` is `contract.encode`.
`label` is the finish event (Requirement extract uses the id). -/
public def OutputContract.extractAudited {α : Type} (contract : OutputContract α)
    (c : Completer) (cfg : ProviderConfig) (prompt : String) (policy : ExtractPolicy := {})
    (runId : String := "run-test") (label : α → String := fun _ => contract.name)
    (backoff : BackoffPolicy := {}) :
    IO Transcript := do
  let base : Transcript := {
    runId
    kind := .extract
    prompt
    providerId := cfg.providerId
    model := cfg.model
    toolsOffered := #[]
    events := #[.repair 0 "placeholder"]
    stop := .transport
  }
  if policy.maxAttempts == 0 then
    return { base with
      events := #[.repair 0 "maxAttempts must be at least 1"]
      stop := .refused 0
    }
  if !nonemptyText prompt then
    return { base with
      events := #[.repair 0 "blank prompt"]
      stop := .refused 0
    }
  -- State: (message history, accumulated audit events). Outcome: the Transcript.
  let init : Array Message × Array Event := (#[{ role := .user, content := prompt }], #[])
  runBounded policy.maxAttempts (init := init)
    (exhausted := fun (_, events) =>
      { base with events := events.push (.repair 0 "no attempt ran"), stop := .refused 0 })
    fun attempt (msgs, events) => do
      let body := Json.compress (chatRequest cfg msgs contract.schema contract.name)
      match ← c.post cfg.chatUrl body with
      | .err e =>
        let events := events.push (.repair (attempt + 1) e.detail)
        if shouldRetryPost e attempt policy.maxAttempts then
          backoff.wait attempt
          pure (.more (appendRepair msgs none e.detail, events))
        else
          pure (.done { base with events, stop := .transport })
      | .ok _status raw =>
        if completionTruncated raw cfg.protocol then
          pure (.done { base with
            events := events.push (.repair (attempt + 1) "truncated")
            stop := .truncated })
        else
          -- Preserve the model's reasoning for this attempt (audit-only).
          let events :=
            match completionReasoning raw cfg.protocol with
            | some r => events.push (.reasoning (attempt + 1) r)
            | none => events
          match acceptFromCompletion contract raw cfg.protocol with
          | .ok a =>
            pure (.done { base with
              events := events.push (.finish (label a))
              outputJson? := some (contract.encode a)
              usage := completionUsage raw cfg.protocol
              stop := .finished })
          | .error e =>
            let events := events.push (.repair (attempt + 1) e.pretty)
            if isLastAttempt attempt policy.maxAttempts then
              pure (.done { base with events, stop := .refused policy.maxAttempts })
            else
              let content? :=
                match messageContent raw cfg.protocol with
                | .ok content => some content
                | .error _ => none
              pure (.more (appendRepair msgs content? (contract.repairHint e), events))

end

end LeanAgent
