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

Split from `lean-spec`. Toolchain: Lean 4.37.0-rc1.

## Validate

```sh
lake build                                        # the LeanAgent library
lake build lean-agent lean-agent-tests multiagent spec-loop # the four executables
lake test
lake check --paranoid                             # Linux only; see below
```

`lake build` also runs the pervasive compile-time `#guard` checks; `lake test`
additionally runs the `lean-agent-tests` binary.

Under Lean 4.35.0, `lake check --paranoid` accepts the library, sandboxed, with
all six bundled checkers (not yet re-run on 4.37.0-rc1), including the verified kernels con-leche and con-ron, and
with only the standard axioms (`propext`, `Quot.sound`, `Classical.choice`). CI
runs it on every merge request, on `main` and on tags. The pure checks that the
kernel can decide are theorems, proved `by decide`: the path rule
(`Files.safeRelPath`), fail-closed field decoding, off-catalog tool refusal, the
usage object's closed keys, the fixture contract's round trip, echo replay
against a tampered result (`LeanAgent/Theorems.lean`, `LeanAgent/Files.lean`),
and the FIPS 180-4 "abc" vector for the transcript digest
(`Sha256.hashBytes_abc`). Those check one input each. The quantified facts are
theorems next to their decoders: `decode` succeeds only on a name the catalog
declares, for every string (`mkToolSet_decode_declared`,
`decodeDemoTool_ok_name`, and the tagged, run-kind, event and stop forms), and
every transcript event and stop reason decodes to itself, for every call id,
output, count and payload (`decodeEvent_encodeEvent`, `decodeStop_encodeStop`,
`decodeTaggedDemoTool_encodeDemoTool`), proved by definitional unfolding alone.
Those are what `lake check` re-verifies, besides the definitions and the
absence of `sorry` and `native_decide`. The remaining `#guard`s and the test binary are evaluated by
the compiler and interpreter at build and test time and are not part of what
the kernels see.

`lake check` sandboxes the build with `bwrap`, so it needs Linux user namespaces. In
Docker that means `--privileged`; on Ubuntu 24.04 it means lifting AppArmor's
`kernel.apparmor_restrict_unprivileged_userns`. Keep the Lean toolchain outside the
project directory, or `lake check` stalls at "Resolving dependencies".
[`docs/lake-check-paranoid-report.md`](docs/lake-check-paranoid-report.md) records
the run, what it does and does not establish, and how the CI job is set up.

## What is checked, and by what

Three columns, because the claims differ in kind. The first is a type: the
value cannot exist. The second is a check that runs at build or test time, or
a theorem the kernel re-verifies. The third is what this package does not
confine, so a caller who needs it must add it outside.

| Claim | Rejected by the type | Checked by `#guard`, theorem or `lake test` | Not confined |
| --- | --- | --- | --- |
| A tool the role did not list | its name is not a constructor of the role's `Tool`; `decode` yields `invalidTag` | theorems `mkToolSet_decode_declared` (every DSL catalog, every string) and `decodeDemoTool_ok_name`; `decode_rejects_off_catalog` on one string; a guard per role | what a listed tool does once it runs |
| Every constructor has a catalog entry, every entry a constructor, names unique | | `ToolSet.covers` guard per catalog on `samples% Tool`, the sample list generated from the inductive | a catalog whose fields are not all strings writes its samples by hand |
| Unknown JSON field, blank value | | theorem `exactFields_rejects_unknown`; theorems `decodeUsage_rejects_*` on the header's usage object; guards per decoder | |
| An unlisted provider | `ProviderId` is a closed inductive | `namedProvider` test | |
| API keys | modeled as env-var names | tests: never in argv, never in the JSONL | the key's use by curl |
| The `ask` loop terminates with a typed `StopReason`, even when a tool throws | | tests: refusal, transport, truncation, throwing runner | |
| Every call of a turn is invoked once and answered once, under its own id and with its own output, in the model's order, and the record stays well-formed | | theorems `turnEventList_invokes`, `turnEventList_results`, `turnEvents_wellFormed` on the pure bookkeeping `askWith` records (`LeanAgent/Transcript.lean`); `lake test`: a throwing runner's call is answered with the error | what a call's output is: the runner's `IO` is not confined, and `askWith` supplying one output per call is a property of the loop, not a theorem |
| A turn's results reach Anthropic as one user message, one `tool_result` per call, in order, right after the turn | | theorem `anthropicMessageList_turn` (every turn, every history before it); `lake test` on a two-call turn | |
| A transcript line read back is the value written | | theorems `decodeEvent_encodeEvent` (every event whose reasoning and tool payload are non-blank, `Event.decodable`), `decodeStop_encodeStop` and `decodeTaggedDemoTool_encodeDemoTool`, at the JSON value level; `lake test` on the JSONL fixtures | the text level: `Json.compress` then `Json.parse` is Lean core's |
| Replay detects a tampered pure-tool result | | theorem `replay_rejects_tampered_result` | observations (`arxiv_search`, files, lake) keep the recorded string |
| The digest covers every line, usage included | | `lake test`: an edited finish or reasoning line, a usage key the encoder never writes, a deleted digest under `DigestPolicy.require` | the digest is not a signature; a decode under `verifyIfPresent` accepts a header with no digest |
| A file tool stays under its root | | theorems on `safeRelPath` (lexical); `lake test` on `Files.confine`, which follows symlinks | a hard link; a path the OS user can reach that the real path check mis-reads |
| A builder run stays in its project | | `lake test`: a project outside the root, or reached through a symlink out of it, is refused; names cannot be flags | the lakefile is a program, and so is the project `lean` elaborates; `lean_check` runs a snippet's `IO` on this host |
| A run is bounded by a timeout | | `lake test`: `Verify.runBounded` kills the process group past the deadline, an orphaned grandchild on the pipe included, and returns within the grace; without a `timeout` or `pgrep` binary | a descendant that leaves the group with its own `setsid` is not signalled; it is not waited on either |
| `ToolEffect` | | `covers` guards that each tool carries its declared effect | `ToolRunner.run` is `Tool → IO String`; the effect is a label the caller checks, not a bound the runner proves |
| The spec loop has no shell | `Workbench` has no shell constructor | guard: `run_command` is refused | `write_file` can replace `./build`, `./test.sh` or `./next`, and `run_script` runs them: for a coding agent that is the point, and the referee's scripts are the confinement |
| `OutputContract` schema and decoder agree | | `OutputContract.ofFields` builds both from one field list; `schemaAgrees` and `roundTrips` guards | a hand-written contract that skips them |
| `requireCite` | | | no catalog in this package marks a tool `isCite`; with these catalogs the flag can only refuse (lean-spec's `show` is the cite tool) |

## Quick start

```sh
# Local Ollama (pull a tool-capable tag first, e.g. qwen3:8b)
LEAN_AGENT_MODEL=qwen3:8b lake exe lean-agent live-ping
LEAN_AGENT_MODEL=qwen3:8b lake exe lean-agent ask
LEAN_AGENT_MODEL=qwen3:8b lake exe lean-agent ask "Search arXiv for category theory in Lean"

# Replay a saved transcript without calling a model (the header must carry a digest)
lake exe lean-agent replay-transcript < fixtures/digested-ask.jsonl
# A transcript written before digests existed needs the flag
lake exe lean-agent replay-transcript --allow-missing-digest < fixtures/extract-theme.jsonl

# The multi-agent example (offline, deterministic)
lake exe multiagent

# The spec loop: builder, referee, reviewer (offline, deterministic)
lake exe spec-loop
```

Stdout is the model's final answer; diagnostics go to stderr. Runs write an
audit transcript under `.lean-agent-audit/` (override with `LEAN_AGENT_AUDIT_DIR`).

## Providers

`LEAN_AGENT_PROVIDER` selects the base config: `ollama` (default),
`bedrock-mantle`, `openai`, `anthropic`, or `glm`. Overlay the model, base URL
and output cap with `LEAN_AGENT_MODEL` / `LEAN_AGENT_BASE_URL` /
`LEAN_AGENT_MAX_TOKENS` (the default cap is 1024; a reasoning model spends it on
its reasoning, so raise it). `LEAN_AGENT_THINKING_BUDGET` turns on Anthropic's
extended thinking with that many tokens of budget; the Messages API requires the
output cap to exceed it. The other providers reason on their own and ignore it.

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
  `OutputContract.ofFields` builds the schema and the unknown-field check from
  one field list; `roundTrips` and `schemaAgrees` state the contract's law.
  Decode failures are repaired up to a bound; truncation is fatal.
* **Closed tool catalogs** — a `ToolSet Tool` is a caller-owned closed algebra;
  a name outside the constructors cannot be invoked. Kernel tools: `echo`,
  `arxiv_search`. Role tools (below): `web_search`, `read_file`, `list_dir`,
  `write_file`, `lean_check`, `toolchain`, `lake_build`, `lake_test`,
  `leanchecker`, `leanchecker_paranoid`.
* **Auditable transcripts** — JSONL, one object per line, with a fail-closed
  decoder, a SHA-256 content digest in the header that the decoder verifies
  (tamper-evident for every line, model free text included), and `replay` that
  re-executes recorded pure-tool results (tamper-evident without trusting the
  writer, for deterministic tools). A tool that throws becomes a tool-error
  result in the transcript, never a lost receipt.
* **Retry classification** — HTTP status is recovered from curl's `-w` output;
  429 and 5xx retry, authentication and other 4xx are fatal, transient network
  failures (timeout, connection reset/refused) retry.

## Traceability

Every run persists, under one `runId`, the user **prompt** (transcript header),
the model **reasoning** for each turn, and the final **output** (`finish` event
and/or structured `outputJson`).

Reasoning is captured as a first-class, audit-only `Event.reasoning` decoded from
provider fields — OpenAI-compatible `reasoning_content` / `reasoning` and
Anthropic `thinking` content blocks. The event is never treated as output and is
ignored by `replay`, so it cannot spoof the tamper-evidence check. Absence of
reasoning is never an error. What goes back to the model is a separate matter:
an Anthropic assistant turn is replayed as the model produced it, signed
`thinking` and `redacted_thinking` blocks included (`Message.contentBlocksJson?`,
filled by `completionReplayBlocks`), because the Messages API refuses a
tool-calling turn whose thinking is missing or altered; the signature never
reaches the transcript. OpenAI-compatible reasoning fields are never re-sent,
since Chat Completions has no place for them.

```jsonl
{"tag":"header","runId":"run-...","kind":"ask","prompt":"...","providerId":"ollama","model":"...","toolsOffered":["arxiv_search"],"spec":null,"digest":"sha256:<64 hex>"}
{"tag":"reasoning","turn":1,"content":"I should search arXiv before answering."}
{"tag":"invoke","callId":"c1","tool":{"tag":"arxiv_search","query":"lean 4"}}
{"tag":"result","callId":"c1","output":"..."}
{"tag":"finish","content":"..."}
{"tag":"stop","reason":"finished"}
```

Two checks cover the record. `replay` re-executes pure tools (`echo`) and compares
the recorded result, which needs no trust in whoever wrote the file but says
nothing about model free text. The header **digest** closes that gap: it is
SHA-256 over the *canonical transcript* — the header without its `digest` key,
then every event line, then the stop line, each rendered by `Json.compress` and
joined by `\n` with no trailing newline (`canonicalJsonlWith`; a transcript
written before 0.3 is exactly this form). `decodeJsonlWith` recomputes it from the
decoded value and refuses a mismatch with `illFormed "header.digest" "mismatch"`,
so an edited `reasoning` or `finish` line, prompt, tool call or stop reason never
decodes, let alone replays. A header without `digest` decodes under
`DigestPolicy.verifyIfPresent`, the library default (older transcripts and
`fixtures/extract-theme.jsonl`), and is refused under `DigestPolicy.require`,
which `replay-transcript` uses unless given `--allow-missing-digest`: deleting
the key is then not a way to make an edited file decode.
`fixtures/digested-ask.jsonl` pins the canonical form. The header's `usage`
object is decoded fail-closed like every other field (`decodeUsage`): a key the
encoder never writes, or a count that is not a number or `null`, is a decode
error, so no text can sit in the raw file outside what the digest covers. SHA-256 is `LeanAgent/Sha256.lean`, pure Lean over
`UInt32`s with no host dependency, so a second Lean program can check a digest
without trusting `shasum`; the FIPS vectors are `#guard`s and the "abc" one is also
a kernel-checked theorem. The digest is not a signature: it detects edits, not a
rewrite by someone who recomputes it.

## Multi-agent

An "agent" is not new machinery — it is a bundle of what the generic `askWith`
loop already takes: a closed `ToolSet`, a system prompt, a `ProviderConfig`, and
a `ToolRunner`. `LeanAgent/Agents.lean` packages that tuple; `LeanAgent/Roles.lean`
defines role-scoped catalogs:

* **market-researcher** — `web_search` only.
* **academic-researcher** — `arxiv_search` only.
* **file-reader** — `read_file` / `list_dir` (no write).
* **file-writer** — `read_file` / `write_file`, sandboxed to a root directory.
* **verifier** — `lean_check`: compile a Lean snippet in a temp directory.
* **builder** — `toolchain`, `lake_build`, `lake_test`, `leanchecker`,
  `leanchecker_paranoid` on a real project inside a sandbox root. Each run is
  bounded by a timeout (enforced in Lean on the whole process group, no
  `timeout` binary needed) and
  returns a verdict with `file:line:column` diagnostics; target and module
  names cannot be flags. Every builder tool is declared with effect `verify`:
  the tools themselves write build artifacts, never sources, git or a store,
  and `covers` checks each carries that label. The label does not bind the
  lakefile, which is a Lean program `lake` runs.
  `lake check --paranoid` is not offered: it needs Linux sandboxing (see Validate).

File tools resolve paths against a sandbox root and reject absolute paths, `~`,
and `..` traversal (`Files.safeRelPath`, lexical), then follow symlinks and
refuse any path whose real location leaves the root (`Files.confine`, before
every read, list or write; a dangling symlink is never written through). A
reader agent simply never offers a write tool, so the capability boundary is
structural. The builder's project path takes the same check; what the project's
lakefile does once `lake` runs it is not confined, and neither is the `IO` a
`lean_check` snippet can run while it elaborates.

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

## The spec loop

`examples/SpecLoop.lean` is lean-spec's builder–referee–reviewer loop on these
pieces. The catalog, referee and finish gate are `LeanAgent/Workbench.lean`, so a
bridge can import them; this example does not import LeanSpec, and its `Finding`
stays local. The **builder** is an `Agent` over a closed `Workbench` catalog (read,
write, list, run a workspace script, pipe an input through the program, run the
spec CLI); there is no shell in the catalog, so the model cannot name one. It
can write `./build`, `./test.sh` or `./next` and then run them, so a shell is one
write away: for a coding agent that is the job, and the confinement is the
referee's scripts and the workspace, not the catalog. The
**referee** is a program: `lake exe spec check`, `./test.sh`, and `./next`, which
releases the next change request only when the tests pass and records the stages
released in `stage.json`; `refereeGate`, the loop's finish hook
(`AskPolicy.onFinish`), reads it after every model finish and either accepts or
nudges the model in the same history. The builder runs on the kernel's one loop,
`askWith`, which runs every tool call of a turn in order and records the turn
through `turnEvents` and `turnResultMessages`, pure functions whose per-call
contract is proved. The **reviewer** is the
read-only `Roles.Reader` agent, and its findings come back through the fail-closed
`OutputContract` as typed `Finding` values (run, requirement, kind, severity,
evidence, note), the row shape of lean-spec's `bench/Findings.lean`.

`lake exe spec-loop` runs it offline against scripted completers and a stub
referee (`fixtures/spec-loop`); `lake exe spec-loop live BENCH TASK LANG ARM SEED
MODEL` drives one lean-spec bench seed with GLM through z.ai, prepares and scores
the workspace with the bench's own scripts, and writes the audited transcript next
to `meta.json`.

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
  Sha256                    — pure SHA-256 for the transcript content digest
  Transcript, Generation    — JSONL audit record, content digest, replay, receipts
  Theorems                  — the decidable checks as kernel-checked theorems
  Samples                   — `samples% T`: a catalog's sample list, generated from its inductive
  Arxiv, WebSearch, Files   — tool implementations (arXiv, web search, sandboxed files)
  Verify, Build             — lean_check; toolchain, lake build/test, leanchecker
  Ask                       — the bounded agent loop
  Roles, Agents             — role catalogs + multi-agent sugar and typed handoff
  Workbench                 — spec-loop builder catalog, referee and finish gate
LeanAgentQuery.lean         — CLI (live-ping | ask | replay-transcript | list-audits)
LeanAgentTests.lean         — runtime test binary
examples/Multiagent.lean    — multi-agent example with typed handoff
examples/SpecLoop.lean      — lean-spec's builder, referee and reviewer loop
fixtures/build-ok, build-fail — tiny packages the builder tests build
fixtures/spec-loop          — stub workspace scripts for the offline spec loop
ci/Dockerfile               — pinned CI image (Lean toolchain + bubblewrap)
docs/                       — lake check --paranoid report
```

This package builds independently and must not import `LeanSpec.*` or
`LeanSpecAgent.*`; a test (`checkImportFirewall`) enforces that.

## Related work

[lean-llmclient](https://github.com/paulbutcher/lean-llmclient), by Paul Butcher,
is a provider-agnostic Lean 4 client for the OpenAI, Anthropic and Bedrock
Converse chat APIs: one request/response vocabulary, a `Provider` interface, and a
pure tool-calling loop with a kernel-checked termination measure, buildable for
the browser as well as natively. It sits at the client layer beneath this
package; the closed catalogs, audit transcripts and structured output here have
no counterpart there, by design. The Anthropic thinking replay above follows its
approach: an assistant turn is kept as the ordered blocks the model produced and
sent back unchanged.

## Public release

A history-free public snapshot is published as
[`bevisera/open-lean-agent`](https://gitlab.com/bevisera/open-lean-agent), with a
read-only [GitHub mirror](https://github.com/Bevisera-AS/open-lean-agent).

## License

Apache License 2.0 — see [LICENSE](LICENSE). Copyright 2026 Bevisera AS
([NOTICE](NOTICE)).
