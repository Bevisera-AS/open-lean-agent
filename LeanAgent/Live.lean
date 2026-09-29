module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Completer
public import LeanAgent.OpenAICompat
public import LeanAgent.Transcript
public meta import LeanAgent.Completer
public meta import LeanAgent.OpenAICompat
public meta import LeanAgent.Transcript

namespace LeanAgent

open Lean

public section

/-- Override `model` / `baseUrl` from the process environment. Secrets stay in env names, not here. -/
public def configFromEnv (base : ProviderConfig) : IO ProviderConfig := do
  let model? ← IO.getEnv "LEAN_AGENT_MODEL"
  let url? ← IO.getEnv "LEAN_AGENT_BASE_URL"
  pure (overlayConfig base model? url?)

/-- Live CLI config. `LEAN_AGENT_PROVIDER` selects the base record; overlays still apply. -/
public def liveConfig : IO (Except String ProviderConfig) := do
  let provider? ← IO.getEnv "LEAN_AGENT_PROVIDER"
  let raw := provider?.getD "ollama"
  let name := if nonemptyText raw then raw else "ollama"
  match namedProvider name with
  | .error e => pure (.error e)
  | .ok base =>
    let cfg ← configFromEnv base
    match cfg.apiKeyEnv with
    | none => pure (.ok cfg)
    | some envName =>
      match ← IO.getEnv envName with
      | none =>
        pure (.error s!"{envName} unset (required for provider {cfg.providerId})")
      | some token =>
        if nonemptyText token then
          pure (.ok cfg)
        else
          pure (.error s!"{envName} unset (required for provider {cfg.providerId})")

public def pingPrompt : String :=
  "Reply with the single word pong."

/-- Envelope-only request. No `response_format`; this is the wire spike, not extract. -/
public def pingRequest (cfg : ProviderConfig) : Json :=
  match cfg.protocol with
  | .openAIChat =>
    Json.mkObj [
      ("model", Json.str cfg.model),
      ("messages", Json.arr #[encodeMessage { role := .user, content := pingPrompt }]),
      ("max_tokens", (cfg.maxTokens.getD 1024 : Json))
    ]
  | .anthropicMessages =>
    Json.mkObj [
      ("model", Json.str cfg.model),
      ("max_tokens", (cfg.maxTokens.getD 1024 : Json)),
      ("messages", Json.arr #[Json.mkObj [
        ("role", Json.str "user"),
        ("content", Json.str pingPrompt)
      ]])
    ]

public def livePing (cfg : ProviderConfig) : IO (Except ExtractError String) := do
  match ← (curlCompleter cfg).post cfg.chatUrl (Json.compress (pingRequest cfg)) with
  | .err e => pure (.error (.transport e.detail))
  | .ok _status raw =>
    if completionTruncated raw cfg.protocol then
      pure (.error .truncated)
    else
      match messageContent raw cfg.protocol with
      | .ok c => pure (.ok c)
      | .error e => pure (.error (.refused e 1))

#guard
  let body := Json.compress (pingRequest ollama)
  body.contains "llama3.2" && body.contains "pong" && !body.contains "Bearer"

#guard
  match namedProvider "bedrock-mantle" with
  | .ok c =>
    c.providerId == "bedrock-mantle" &&
      c.apiKeyEnv == some "AWS_BEARER_TOKEN_BEDROCK" &&
      (overlayConfig c (some "eu.amazon.nova-lite-v1:0") none).model == "eu.amazon.nova-lite-v1:0" &&
      (overlayConfig c (some "eu.amazon.nova-lite-v1:0") none).chatUrl == c.chatUrl
  | .error _ => false

#guard
  match namedProvider "openai" with
  | .ok c => c.providerId == "openai" && c.apiKeyEnv == some "OPENAI_API_KEY"
  | .error _ => false

#guard
  let body := Json.compress (pingRequest anthropic)
  body.contains "claude-sonnet-4-5" && body.contains "max_tokens" && !body.contains "response_format"

#guard
  match namedProvider "langchain" with
  | .error d => d.contains "langchain"
  | .ok _ => false

end

end LeanAgent
