import Lean.Data.Json
import LeanAgent.Agents
import LeanAgent.Roles
import LeanAgent.Concurrent
import LeanAgent.OpenAICompat
import LeanAgent.Anthropic

/-!
# Multi-agent example: typed handoff, local + Bedrock

Three agents, each with its own *closed* tool catalog:

* `marketAgent`   — a market-researcher that can only `web_search`.
* `academicAgent` — an academic-researcher that can only `arxiv_search`.
* `writerAgent`   — a file-writer that can `read_file` / `write_file` in a sandbox.

The handoff between agents is a **Lean type**, `MarketBrief`, carried through the
fail-closed `OutputContract` extract path — not free-form markdown. Downstream
agents receive either the Lean value (rendered into their prompt) or its
canonical JSON via `handoffJson`.

Run offline (deterministic, scripted models):

```sh
lake exe multiagent
```

The `liveOllama` / `liveBedrock` functions at the bottom show the same pipeline
against real providers; they are not called by `main` so the example stays
hermetic.
-/

open Lean
open LeanAgent
open LeanAgent.Roles

/-! ## The typed handoff object -/

/-- What the market-researcher hands to the next agent. A real Lean value with a
fail-closed JSON contract, so the boundary is type-checked, not stringly-typed. -/
structure MarketBrief where
  topic : String
  marketSizeUsd : Nat
  competitors : Array String
  deriving Repr, BEq

def encodeBrief (b : MarketBrief) : Json :=
  Json.mkObj [
    ("topic", Json.str b.topic),
    ("marketSizeUsd", (b.marketSizeUsd : Json)),
    ("competitors", Json.arr (b.competitors.map Json.str))
  ]

def decodeBrief (j : Json) : Except DecodeError MarketBrief := do
  let o ← asObj "market_brief" j
  exactFields "market_brief" ["topic", "marketSizeUsd", "competitors"] o
  let topic ← strField "market_brief" "topic" j
  let size ← natField "market_brief" "marketSizeUsd" j
  let competitors ← arrStrField "market_brief" "competitors" j
  if nonemptyText topic then pure { topic, marketSizeUsd := size, competitors }
  else .error (.illFormed "market_brief.topic" "blank")

/-- The contract ties the JSON schema, the Lean decode/encode, and the
well-formedness predicate together. -/
def marketBrief : OutputContract MarketBrief := {
  name := "market_brief"
  schema := Json.mkObj [
    ("type", Json.str "object"),
    ("properties", Json.mkObj [
      ("topic", Json.mkObj [("type", Json.str "string")]),
      ("marketSizeUsd", Json.mkObj [("type", Json.str "integer")]),
      ("competitors", Json.mkObj [
        ("type", Json.str "array"),
        ("items", Json.mkObj [("type", Json.str "string")])
      ])
    ]),
    ("required", Json.arr #[Json.str "topic", Json.str "marketSizeUsd", Json.str "competitors"]),
    ("additionalProperties", Json.bool false)
  ]
  decode := decodeBrief
  encode := encodeBrief
  wellFormed := fun b => nonemptyText b.topic && b.competitors.size > 0
  repairHint := defaultRepairHint "market_brief"
}

/-- Render a `MarketBrief` into a prompt for the academic agent. Type-checked
handoff: the downstream prompt is derived from the Lean value's fields. -/
def briefToAcademicPrompt (b : MarketBrief) : String :=
  s!"Find academic work relevant to the commercial topic \"{b.topic}\". " ++
    s!"Known competitors: {joinSep ", " b.competitors.toList}. " ++
    "Search arXiv and cite ids and titles."

/-! ## Agent definitions (config only; no new orchestration) -/

def sandboxRoot : System.FilePath := ".lean-agent-sandbox"

def marketAgent (cfg : ProviderConfig) : Agent Market := {
  name := "market-researcher"
  system :=
    "You are a market researcher. Call web_search to gather market size, " ++
      "competitors, and pricing. Then answer."
  cfg
  tools := marketTools
  runner := marketRunner
}

def academicAgent (cfg : ProviderConfig) : Agent Academic := {
  name := "academic-researcher"
  system :=
    "You are an academic researcher. Call arxiv_search for related work, " ++
      "then cite ids and titles from the result."
  cfg
  tools := academicTools
  runner := academicRunner
}

def writerAgent (cfg : ProviderConfig) : Agent Writer := {
  name := "file-writer"
  system :=
    "You are a report writer. Use write_file to save the report to the given " ++
      "relative path, then confirm what you wrote."
  cfg
  tools := writerTools
  runner := writerRunner sandboxRoot
}

def verifierAgent (cfg : ProviderConfig) : Agent Verifier := {
  name := "verifier"
  system :=
    "You are a Lean 4 verifier. Call lean_check on any snippet you are given and " ++
      "report whether it compiles."
  cfg
  tools := verifierTools
  runner := verifierRunner 30
}

/-! ## Scripted (offline) completers

Each `Completer` returns canned provider responses so the whole pipeline runs
deterministically. In production you pass `curlCompleter agent.cfg` instead.
-/

/-- Return the given replies in order; error once the script is exhausted. -/
def scripted (replies : List String) : IO Completer := do
  let box ← IO.mkRef replies
  pure {
    post := fun _url _body => do
      match ← box.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest => box.set rest; pure (.ok 200 r)
  }

def main : IO UInt32 := do
  -- Any provider config works; the closed tool sets are provider-agnostic.
  let cfg := ollama

  -- 1) Market researcher: web_search, then a structured MarketBrief.
  let marketC ← scripted [
    wrapToolCall "m1" "web_search" "{\"query\":\"lean theorem prover market\"}",
    wrapContent "Gathered market data; summarizing."
  ]
  let mAgent := marketAgent cfg
  let mT ← mAgent.run marketC "Research the market for Lean-based verification tooling." "run-market"
  IO.eprintln s!"[{mAgent.name}] stop={repr mT.stop} events={mT.events.size}"

  -- The brief is produced through the *typed* extract path (its own model turn).
  let briefC ← scripted [
    wrapContent (Json.compress (encodeBrief {
      topic := "Lean-based verification tooling"
      marketSizeUsd := 4200000000
      competitors := #["Coq", "Isabelle", "F*"]
    }))
  ]
  let brief ← match ← extractTyped marketBrief briefC cfg
      "Summarize the market as a market_brief JSON object." with
    | .ok b => pure b
    | .error e => do IO.eprintln s!"brief failed: {e.pretty}"; return 1
  IO.eprintln s!"[handoff] MarketBrief (Lean value): {repr brief}"
  IO.eprintln s!"[handoff] MarketBrief (canonical JSON): {handoffJson marketBrief brief}"

  -- 2) Academic researcher receives the TYPED brief (rendered from Lean fields).
  let academicC ← scripted [
    wrapToolCall "a1" "arxiv_search" "{\"query\":\"Lean 4 verification\"}",
    wrapContent "Relevant: 'Lean Demo' (arXiv:2401.00001) on verified tooling."
  ]
  let aAgent := academicAgent cfg
  let aT ← aAgent.run academicC (briefToAcademicPrompt brief) "run-academic"
  let academicFindings := (Agent.finalText aT).getD "(no findings)"
  IO.eprintln s!"[{aAgent.name}] {academicFindings}"

  -- 3) File writer persists a combined report. The handoff to the writer is the
  --    canonical JSON of the brief plus the academic findings — still structured.
  let reportPath := "reports/lean-market.json"
  let reportBody := Json.compress (Json.mkObj [
    ("brief", encodeBrief brief),
    ("academic", Json.str academicFindings)
  ])
  let writerC ← scripted [
    wrapToolCall "w1" "write_file"
      (Json.compress (Json.mkObj [
        ("path", Json.str reportPath),
        ("content", Json.str reportBody)
      ])),
    wrapContent s!"Wrote the combined report to {reportPath}."
  ]
  let wAgent := writerAgent cfg
  let wT ← wAgent.run writerC
    s!"Write a JSON report combining the market brief and academic findings to {reportPath}."
    "run-writer"
  IO.eprintln s!"[{wAgent.name}] stop={repr wT.stop}"

  -- Show the file actually landed in the sandbox (writerRunner enforces the root).
  let written ← Files.readFileIn sandboxRoot reportPath
  IO.println written

  -- 4) Concurrency: run the verifier in the BACKGROUND on a produced Lean snippet
  --    while the main thread keeps working, then join. The verifier really shells
  --    out to `lean`, so this is a genuine parallel compile.
  let snippet := "def leanMarketShare : Nat := 42\n#eval leanMarketShare"
  let verifyC ← scripted [
    wrapToolCall "v1" "lean_check" (Json.compress (Json.mkObj [("code", Json.str snippet)])),
    wrapContent "The snippet compiles."
  ]
  let vAgent := verifierAgent cfg
  let vHandle ← vAgent.runInBackground verifyC s!"Does this compile?\n{snippet}" "run-verify"
  IO.eprintln "[main] verifier launched in background; continuing other work…"
  -- (other work could happen here concurrently)
  let vT ← await vHandle
  IO.eprintln s!"[{vAgent.name}] stop={repr vT.stop} verdict={(Agent.finalText vT).getD "?"}"

  -- 5) Fan-out: several same-role agents at once (fanOut is homogeneous in the
  --    tool type, so it batches one role). Order is preserved.
  let mC1 ← scripted [wrapContent "Market segment A: growing."]
  let mC2 ← scripted [wrapContent "Market segment B: flat."]
  let results ← fanOut #[
    (marketAgent cfg).run mC1 "Read segment A." "run-fan-a",
    (marketAgent cfg).run mC2 "Read segment B." "run-fan-b"
  ]
  IO.eprintln s!"[fan-out] {results.size} market agents completed concurrently"

  -- Heterogeneous parallelism uses independent handles (different tool types
  -- cannot share one fanOut array — the type system keeps each closed).
  let aC2 ← scripted [wrapContent "Academic: active area."]
  let aHandle ← (academicAgent cfg).runInBackground aC2 "One-line academic read." "run-bg-academic"
  let aBg ← await aHandle
  IO.eprintln s!"[bg] academic finished: {(Agent.finalText aBg).getD "?"}"
  return 0

/-! ## Live variants (not invoked by `main`)

The only difference between local and Bedrock is the `ProviderConfig`; the closed
tool sets, the agent loop, and the typed handoff are identical.

* Local Ollama needs no API key — pull a tool-capable tag first (e.g. `qwen3:8b`).
* Bedrock (Mantle OpenAI-compat endpoint) reads `AWS_BEARER_TOKEN_BEDROCK`.
-/

def liveOllama : IO Unit := do
  let cfg := overlayConfig ollama (some "qwen3:8b") none
  let a := marketAgent cfg
  let t ← a.runLive "Research the market for Lean-based verification tooling."
  IO.println ((Agent.finalText t).getD "(no answer)")

def liveBedrock : IO Unit := do
  let cfg := overlayConfig bedrockMantle (some "eu.amazon.nova-lite-v1:0") none
  let a := academicAgent cfg
  let t ← a.runLive "Find related work on dependently-typed program verification."
  IO.println ((Agent.finalText t).getD "(no answer)")
