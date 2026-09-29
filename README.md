# lean-agent

A thin, fail-closed agent layer for Lean 4. Provider-neutral HTTP, closed tool
catalogs, typed structured output, auditable transcripts, and a bounded `ask`
loop — with connectors to local Ollama, AWS Bedrock (Mantle OpenAI-compat),
OpenAI, Anthropic, and GLM.

The design leans on the type system: providers and tools are closed inductives,
so an unlisted provider or an invented tool name is a compile-time or decode-time
error, never a silent runtime path. JSON decoding is fail-closed (unknown fields
are rejected). Secrets are modeled as environment-variable *names*, never values,
and never appear in process arguments or transcripts.

Split from `lean-spec`. Same toolchain: Lean 4.33.

## Validate

```sh
lake build && lake test
```

`lake build` also runs the pervasive compile-time `#guard` checks; `lake test`
additionally runs the `lean-agent-tests` binary.

## Quick start

```sh
# Local Ollama (pull a tool-capable tag first, e.g. qwen3:8b)
LEAN_AGENT_MODEL=qwen3:8b lake exe lean-agent live-ping
LEAN_AGENT_MODEL=qwen3:8b lake exe lean-agent ask
LEAN_AGENT_MODEL=qwen3:8b lake exe lean-agent ask "Search arXiv for category theory in Lean"

# Replay a saved transcript without calling a model
lake exe lean-agent replay-transcript < fixtures/extract-theme.jsonl

# The multi-agent example (offline, deterministic)
lake exe multiagent
```

Stdout is the model's final answer; diagnostics go to stderr. Runs write an
audit transcript under `.lean-agent-audit/` (override with `LEAN_AGENT_AUDIT_DIR`).

## Providers

`LEAN_AGENT_PROVIDER` selects the base config: `ollama` (default),
`bedrock-mantle`, `openai`, `anthropic`, or `glm`. Overlay the model and base URL
with `LEAN_AGENT_MODEL` / `LEAN_AGENT_BASE_URL`.

| Provider        | Protocol            | API key env               |
| --------------- | ------------------- | ------------------------- |
| `ollama`        | OpenAI Chat         | none (local)              |
| `bedrock-mantle`| OpenAI Chat         | `AWS_BEARER_TOKEN_BEDROCK`|
| `openai`        | OpenAI Chat         | `OPENAI_API_KEY`          |
| `glm`           | OpenAI Chat         | `GLM_API_KEY`             |
| `anthropic`     | Anthropic Messages  | `ANTHROPIC_API_KEY`       |

Ollama, Bedrock Mantle, OpenAI, and GLM share the Chat Completions encoder.
Anthropic uses the Messages URL, `x-api-key`, `tool_use` blocks, and a system
schema instruction instead of `response_format`. The provider is chosen by
config only — the tool catalogs, the agent loop, and structured output are all
provider-agnostic.

## What's in the box

* **Bounded `ask` loop** — offers a closed tool catalog, runs tools, and always
  returns a typed `Transcript` with a `StopReason` (`finished` / `refused n` /
  `transport` / `truncated`).
* **Structured output (`extract`)** — Instructor-style. An `OutputContract α`
  ties a JSON schema to a Lean decode/encode plus a well-formedness predicate.
  Decode failures are repaired up to a bound; truncation is fatal.
* **Closed tool catalogs** — a `ToolSet Tool` is a caller-owned closed algebra;
  a name outside the constructors cannot be invoked. Kernel tools: `echo`,
  `arxiv_search`. Role tools (below): `web_search`, `read_file`, `list_dir`,
  `write_file`.
* **Auditable transcripts** — JSONL, one object per line, with a fail-closed
  decoder and `replay` that re-checks recorded pure-tool results (tamper-evident
  for deterministic tools).
* **Retry classification** — HTTP status is recovered from curl's `-w` output;
  429 and 5xx retry, authentication and other 4xx are fatal, transient network
  failures (timeout, connection reset/refused) retry.

## Traceability

Every run persists, under one `runId`, the user **prompt** (transcript header),
the model **reasoning** for each turn, and the final **output** (`finish` event
and/or structured `outputJson`).

Reasoning is captured as a first-class, audit-only `Event.reasoning` decoded from
provider fields — OpenAI-compatible `reasoning_content` / `reasoning` and
Anthropic `thinking` content blocks. It is never fed back to the model, never
treated as output, and is ignored by `replay`, so it cannot spoof the
tamper-evidence check. Absence of reasoning is never an error.

```jsonl
{"tag":"header","runId":"run-...","kind":"ask","prompt":"...","providerId":"ollama","model":"...","toolsOffered":["arxiv_search"],"spec":null}
{"tag":"reasoning","turn":1,"content":"I should search arXiv before answering."}
{"tag":"invoke","callId":"c1","tool":{"tag":"arxiv_search","query":"lean 4"}}
{"tag":"result","callId":"c1","output":"..."}
{"tag":"finish","content":"..."}
{"tag":"stop","reason":"finished"}
```

> Replay gives tamper-evidence for pure tool results only. Model free-text
> (reasoning and `finish`) is on the record but not integrity-checked; a content
> digest over the canonical transcript would close that gap.

## Multi-agent

An "agent" is not new machinery — it is a bundle of what the generic `askWith`
loop already takes: a closed `ToolSet`, a system prompt, a `ProviderConfig`, and
a `ToolRunner`. `LeanAgent/Agents.lean` packages that tuple; `LeanAgent/Roles.lean`
defines role-scoped catalogs:

* **market-researcher** — `web_search` only.
* **academic-researcher** — `arxiv_search` only.
* **file-reader** — `read_file` / `list_dir` (no write).
* **file-writer** — `read_file` / `write_file`, sandboxed to a root directory.

File tools resolve paths against a sandbox root and reject absolute paths, `~`,
and `..` traversal (`Files.safeRelPath`). A reader agent simply never offers a
write tool, so the capability boundary is structural.

### Typed handoff (Lean value or JSON, not markdown)

Results pass between agents as **Lean types**, not free text. A producing agent
yields an `α` through the fail-closed `OutputContract` extract path; the consuming
agent receives either the Lean value (rendered into its prompt) or the contract's
canonical JSON.

```lean
-- The handoff object is a real Lean type with a fail-closed JSON contract.
structure MarketBrief where
  topic : String
  marketSizeUsd : Nat
  competitors : Array String

-- Agent A produces a typed MarketBrief via extract (its own model turn):
let brief ← match ← extractTyped marketBrief briefC cfg
    "Summarize the market as a market_brief JSON object." with
  | .ok b => pure b
  | .error e => ...

-- Hand it to Agent B as a Lean value (type-checked prompt derivation) ...
let aT ← academicAgent cfg |>.run academicC (briefToAcademicPrompt brief)

-- ... or as canonical JSON when the downstream should see exact fields:
let json := handoffJson marketBrief brief   -- {"competitors":[...],"marketSizeUsd":...,"topic":"..."}
```

See `examples/Multiagent.lean` for the full market → academic → writer pipeline.
It runs offline against scripted completers (`lake exe multiagent`); switching to
real providers is a one-line change — `curlCompleter agent.cfg` — with `liveOllama`
and `liveBedrock` at the bottom of the file showing local and Bedrock variants.

## Layout

```
LeanAgent/
  Util, JsonCore, Json      — helpers and the fail-closed JSON decode DSL
  Provider, Types           — closed provider catalog, messages, error types
  Curl, Completer           — HTTP via curl (secrets in a temp header file); the model seam
  ToolSpec, ToolSet, Tools  — tool schema, closed tool algebra, kernel catalog + ToolRunner
  Anthropic, OpenAICompat   — per-protocol request/response encoders + reasoning extraction
  Step, Retry               — decode a model move; classify failures / repair
  OutputContract, Extract   — structured output (Instructor-style) + audited extract
  Transcript, Generation    — JSONL audit record, replay, receipts
  Arxiv, WebSearch, Files   — tool implementations (arXiv, web search, sandboxed files)
  Ask                       — the bounded agent loop
  Roles, Agents             — role catalogs + multi-agent sugar and typed handoff
LeanAgentQuery.lean         — CLI (live-ping | ask | replay-transcript)
LeanAgentTests.lean         — runtime test binary
examples/Multiagent.lean    — multi-agent example with typed handoff
```

This package builds independently and must not import `LeanSpec.*` or
`LeanSpecAgent.*`; a test (`checkImportFirewall`) enforces that.

## Source

Canonical hosting is on GitLab (`bevisera/open-lean-agent`). A read-only
[GitHub mirror](https://github.com/Bevisera-AS/open-lean-agent) is kept in sync
for discovery and tooling that expects GitHub; open issues and PRs against GitLab
when you can.

## License

Apache License 2.0 — see [LICENSE](LICENSE). Copyright 2026 Bevisera AS
([NOTICE](NOTICE)).
