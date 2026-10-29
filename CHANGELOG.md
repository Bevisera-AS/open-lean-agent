# Changelog

All notable changes to **lean-agent** are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Unless noted otherwise, every release builds clean (`lake build`) and passes the
suite (`lake test`), with no `sorry` and no `native_decide`. From 0.2.0,
`lake check --paranoid` accepts the library with only the three standard
axioms (`propext`, `Quot.sound`, `Classical.choice`).

## [0.4.0] — 2026-10-29

### Added
- **Transcript content digest** (`LeanAgent/Sha256.lean`, `LeanAgent/Transcript.lean`).
  The audit header now carries `"digest":"sha256:<hex>"`, SHA-256 over the canonical
  transcript: the header without `digest`, then every event line and the stop line,
  `Json.compress`ed and joined by `\n` (`canonicalJsonlWith`, `digestWith`).
  `decodeJsonlWith` recomputes it from the decoded value and refuses a mismatch
  (`illFormed "header.digest" "mismatch"`; an unknown algorithm prefix is
  `"unsupported algorithm"`), so model free text — `reasoning` and `finish` — is now
  integrity-checked, not only the pure-tool results `replay` re-executes. A header
  without `digest` still decodes, so existing transcripts and
  `fixtures/extract-theme.jsonl` are unchanged; `fixtures/digested-ask.jsonl` pins the
  canonical form. `headerDigest?` reads the declared digest without decoding;
  `replay-transcript` reports whether one was verified. The audit index row carries
  the digest (`AuditEntry.digest`, `null` or absent on older rows).
- **SHA-256 in pure Lean** (`LeanAgent.Sha256`): `UInt32` arithmetic over
  `Array UInt8`, structural recursion only, no host dependency, so a second Lean
  program can check a digest without trusting `shasum`. The FIPS 180-4 vectors
  (empty, "abc", the two-block 56-byte message, a 64-byte message) are `#guard`s, and
  `Sha256.hashBytes_abc` proves the "abc" vector by `decide +kernel` — the kernel
  reduces the whole hash in about a second, so it is a theorem, not only a guard.
- **Builder role** (`Roles.Builder`, `LeanAgent.Build`): `toolchain`, `lake_build`,
  `lake_test`, `leanchecker` and `leanchecker_paranoid`, run on a real project inside a
  sandbox root. A project path follows the `Files` rule (no absolute paths, `~` or `..`);
  target and module names cannot be flags; every run is bounded by a timeout. The
  result is a `Build.Verdict` with diagnostics parsed into file, line and column (both
  lake's `error: f.lean:4:15: …` and lean's `f.lean:4:15: error: …`), never an
  exception. All five tools have effect `verify`; there are no git or write tools.
- Fixture packages `fixtures/build-ok` and `fixtures/build-fail`, which the test
  binary builds, tests and kernel-checks.
- **Spec loop example** (`examples/SpecLoop.lean`, `lake exe spec-loop`): lean-spec's
  builder–referee–reviewer loop. The builder is an `Agent` over a closed `Workbench`
  catalog (no shell), driven by `runBuilder`, a `runBounded` loop that keeps the
  history across the referee's nudges; the referee is the workspace scripts and the
  `stage.json` gate `./next` writes; the reviewer is `Roles.Reader` with findings
  extracted through a fail-closed `OutputContract` (`Finding`: run, requirement,
  kind, severity 1–3, evidence, note). Offline it runs against scripted completers
  and the stub referee in `fixtures/spec-loop`, in CI; `spec-loop live` drives one
  lean-spec bench seed with GLM and scores it with the bench's own scripts.

- **Theorems** (`LeanAgent/Theorems.lean`, `LeanAgent/Files.lean`): the decidable
  checks as theorems proved `by decide`, so `lake check` re-verifies them with the
  kernel: `safeRelPath` on the guard cases, `exactFields` on an unknown field,
  `decodeDemoTool` on an off-catalog name, an unknown field and a blank value,
  `boolFlag`'s round trip and closed schema, and echo `replay` against a tampered
  result. `Theorems.lean` is a legacy (non-`module`) file on purpose: in a module
  file `decide` cannot unfold `Lean.Data.Json`.
- `ToolSet.covers` and `ToolSet.uniqueNames`: a catalog covers its inductive on a
  list of samples (unique names, every sample named and round-tripping through the
  tagged form, every spec named by a sample). Every catalog in the package and the
  examples `#guard`s it with one sample per constructor, so a missing `project`
  arm, a dead declaration or a duplicate name is a build error instead of a silent
  empty name and `.read` effect.
- `Files.confine`: after the lexical rule, the real path (symlinks followed) of a
  file, or of its nearest existing ancestor, must stay under the real root, and a
  dangling symlink is never written through. `readFileIn`, `listDirIn`,
  `writeFileIn` and the builder's `projectDirIO` use it.
- `OutputContract.ofFields` builds a flat object contract from one field list:
  the schema's `properties`, `required` and `additionalProperties: false` and the
  decoder's `exactFields` check come from the same list. `OutputContract.roundTrips`
  and `schemaAgrees` state the contract's law; `closedObjectFields` reads a schema's
  required fields. `boolFlag`, the example `MarketBrief` and the spec loop's
  `Finding` contracts use them, with guards.
- A "What is checked, and by what" table in the README: rejected by the type,
  checked by a guard, theorem or `lake test`, or not confined.

- **Multi-call turns** (`ModelTurn`, `turnFromCompletionWith`): a completion with
  several tool calls (OpenAI Chat `tool_calls`, Anthropic `tool_use` blocks) decodes
  as one turn, in the model's order, failing closed on an invented name anywhere in
  it, a blank id or a duplicate id. `askWith` runs the calls in order and records an
  `invoke`/`result` pair for each, posting one assistant message with every call and
  one tool message per call. `ModelStep` and `stepFromCompletionWith` keep the
  one-move view and still refuse `more than one tool call`. `Transcript.eventsGo_pair`
  and `eventsGo_two_calls` prove that pairs recorded this way keep `eventsWellFormed`;
  `wrapToolCalls`, `wrapAnthropicToolUses` and `ToolSet.assistantInvokesMessage` are
  the multi-call forms of the existing helpers.
- **Finish gate** (`AskPolicy.onFinish`, `FinishInfo`, `FinishVerdict`): after a
  finish passes the kernel checks, a caller's hook may accept it or nudge: the detail
  becomes a repair event, the reply the next user message in the same history. A
  nudge on the last turn, a blank reply or a throwing gate is a refusal; `maxTurns`
  bounds the nudges. `AskPolicy` is now indexed by the tool type (`AskPolicy Tool`,
  defaulting to `DemoTool`) so the gate sees the typed events.

- **`DigestPolicy`** (`decodeJsonlWith`, `decodeJsonl`): `verifyIfPresent`, the
  default, accepts a header without `digest` as before; `require` refuses it with
  `illFormed "header.digest" "missing"`, so an edited transcript cannot be made to
  decode by deleting its digest. `replay-transcript` requires a digest unless given
  `--allow-missing-digest`.
- **`samples% T`** (`LeanAgent.Samples`): one value per constructor of a closed
  inductive, every field `"sample"`, as a term. Every catalog's `covers` guard now
  takes `samples% Tool` instead of a hand-kept list, so a new constructor is in the
  check when it is declared. A field that is not a string is an elaboration error
  naming it.
- **Quantified decoder lemmas**, next to the decoders they are about, so `lake
  check` re-verifies a statement about every input rather than one string:
  `mkToolSet_decode_declared` and `mkToolSet_decodeTagged_declared` (a DSL catalog
  decodes only a declared name or tag) with `mkToolSet_decode_off_catalog`;
  `decodeDemoTool_ok_name`, `decodeDemoTool_off_catalog` and
  `decodeTaggedDemoTool_ok_tag` (the kernel catalog decodes only `echo` and
  `arxiv_search`, and returns that constructor); `decodeRunKind_ok`,
  `decodeEventWith_ok_tag` and `decodeStop_ok_reason`. `Event.tag` and
  `StopReason.reason` name the wire tags the statements use. The `decide`
  theorems in `Theorems.lean` stay as the one-input checks.
- `decodeUsage_*` theorems: the header's usage object accepts counts and `null`,
  and refuses an unknown key, a non-object and a non-numeric count.

### Changed
- **`decodeUsage` is fail-closed.** The header's `usage` object was the one place
  the decoder ignored what it did not understand: an unknown key or an ill-typed
  count was dropped, so `"usage":{"note":"edited"}` decoded to an empty usage, the
  canonical form omitted it, and the stored digest still matched. It is now
  `Except DecodeError Usage`: the keys are exactly `usageFields`, a count is a
  natural number or `null`, and anything else is `unknownFields`, `expectedObject`
  or `wrongType` under `header.usage`.
- **`Verify.runBounded` bounds the process tree.** The child is spawned in its own
  session and process group (`setsid`); past the deadline the group gets `TERM`
  through Lean and then `KILL` through the shell's built-in `kill`, so every
  descendant that stayed in the group is stopped, however deep. It no longer
  terminates direct children by `pgrep -P`, which the CI image does not have. The
  pipes are drained in chunks into buffers and the call returns within the
  deadline plus a grace (`graceMs`, 2 s) with what was read, rather than blocking
  on `readToEnd` until every holder of the pipe is gone. A child that exits while
  a descendant still holds the pipe is given until the deadline, then the group
  is killed and the run counts as timed out. A descendant that left the group
  with its own `setsid` is neither signalled nor waited on.
- **One agent loop.** `examples/SpecLoop.lean` no longer carries its own copy of
  the loop: `runBuilder`, `parallelCalls` and `LoopState` are gone, and the builder
  runs through `Agent.run` with the referee's stage gate as `AskPolicy.onFinish`
  (`refereeGate`). Retry, truncation, reasoning and transcript handling cannot drift
  between the kernel and the example any more. `lake exe spec-loop` is unchanged in
  output.
- `Transcript.eventsWellFormed`'s state machine is the top-level `Transcript.eventsGo`
  (same results), so theorems can be stated about it.
- `Verify.runBounded` enforces the bound in Lean: it polls the child and, past
  the deadline, kills its process group (above). It no longer depends on a
  `timeout` or `gtimeout` binary, so the bound holds on a Mac without coreutils.
  Shared by `leanCheck`, the builder tools and the spec loop's referee.
- `nonemptyText`, `safeRunId` and `safeRelPath` are stated over character lists
  (same results) and `@[expose]`d, so the kernel can decide them.
- The cite repair messages name no tool: `requireCite` is only meaningful with a
  catalog that marks a tool `isCite`, which none in this package does; the policy
  doc says so.
- The builder and verifier docs state what the sandbox root does not confine: the
  lakefile and the project `lean` elaborates are programs, and a `lean_check`
  snippet runs `IO` on the host.

- `encodeHeader` takes an optional digest; `AuditEntry.ofTranscriptWith` takes the
  `ToolSet` first, to compute the digest. `encodeJsonlWith` output now has the
  `digest` key in the header; the pre-digest form is `canonicalJsonlWith`.

### Fixed
- `askWith` catches a throwing `ToolRunner.run`: the exception becomes the tool's
  result event, visible to the model, and the transcript is still written. Before,
  a throw skipped the audit entirely.
- The test "reasoning is not sent back to the provider" was vacuous (it folded every
  event to `true`). It now runs a two-turn scripted ask and asserts the second
  request body carries the tool call and result but not the first turn's reasoning.

## [0.2.1] — 2026-10-18

### Fixed
- **Root module `LeanAgent`.** `LeanAgent.lean` imports every public module, and the
  library builds it. A package that precompiles its dependencies
  (`precompileModules := true`, as bevisera-business-kb does) loads `LeanAgent` as a
  shared library, which must contain a module of that name; without it the build
  failed with `initializer not found 'initialize_lean_x2dagent_LeanAgent'`.
  `import LeanAgent` now brings in the whole library.

## [0.2.0] — 2026-10-17

### Added
- **CI.** `.gitlab-ci.yml` runs `verify` (build the library and the three
  executables, then `lake test`) and `kernel-check` on merge requests, on `main`, on
  tags and on "Run pipeline" from the GitLab UI. `.github/workflows/ci.yml` runs the
  same two jobs on the GitHub mirror of open-lean-agent.
- **`kernel-check` runs `lake check --paranoid`, sandboxed.** It replays the library
  through all six checkers bundled with Lean: its kernel, its hardened-allocator
  variant, lean4lean, nanoda, and the verified kernels con-leche and con-ron. It
  fails on any rejection or non-standard axiom and keeps the log as an artifact. It
  needs a runner that starts containers privileged, because `bwrap` needs user
  namespaces. Confirmed locally in the CI image: all six accept 67,092 declarations.
- The CI image (`ci/Dockerfile`): Debian, Lean 4.35.0, `bubblewrap` and `/run/user`.
  The manual `build-ci-image` job pushes it to the Container Registry for pinning by
  digest.
- `docs/lake-check-paranoid-report.md`: the run, what it does and does not establish
  (lean-agent has no theorems; the `#guard`s are not re-checked by the kernels), and
  how the sandbox and CI are set up.
- `ToolEffect` (`read | propose | commit | summarize | verify`) on `ToolDecl` and
  `ToolSet`, defaulting to `read`. A caller can confine an agent's closed catalog to
  the effects its role permits, e.g. state that it contains no committing tool.
  Additive; existing tools are unaffected.

### Changed (build)
- **The library is the default target, the executables are not.** `lake build`
  builds `LeanAgent`; build the executables with
  `lake build lean-agent lean-agent-tests multiagent`. `lake check` imports every
  default target together and each executable defines `main`; it also means the
  whole library is checked, not only what the CLI imports.

### Changed
- Toolchain is Lean 4.35.0 (was 4.33.0). No source changes were needed.
- License is Apache 2.0 (was MIT); Bevisera AS is the copyright holder (`NOTICE`).

## [0.1.1] - 2026-08-30

### Added
- `Concurrent.lean`: `runInBackground`/`await`, `fanOut` for independent agents in
  parallel, and a typed single-slot `Mailbox` so a Lean value crosses between agents
  as a value, not a prompt string.
- A Verifier role (`lean_check`, `Verify.lean`) that compiles a Lean snippet with
  `lake env lean` in a temp directory, bounded by `timeout` when available.
- `AuditIndex.lean`: a rebuildable `index.jsonl` manifest over the audit
  transcripts, with query helpers and the `list-audits` CLI subcommand. Run ids get
  a random suffix so same-millisecond runs no longer collide; transcripts are
  written atomically.
- `ToolDSL.lean`: `mkToolSet` builds a fail-closed `ToolSet` from compact
  declarations. The Academic, Market, Reader, Writer and Verifier roles use it;
  behaviour is unchanged.
- Token usage (OpenAI and Anthropic) is recorded on the transcript and the
  generation receipt; exponential backoff with jitter on retryable failures.

### Changed
- The transport returns a typed `HttpResult` instead of `Except String`; retries
  are classified on the numeric HTTP status.
- The retry and repair loops of `extract`, `extractAudited` and `ask` share one
  bounded-loop combinator (`Loop.lean`). Behaviour is unchanged.

## [0.1.0] - 2026-08-28

First release: the provider-neutral agent kernel split out of lean-spec.

### Added
- Closed provider catalog (Ollama, Bedrock Mantle, OpenAI, Anthropic, GLM), HTTP via
  curl with secrets passed in a temp header file, fail-closed JSON decoding.
- Closed tool catalogs, typed structured output (`OutputContract`, `extract`), the
  bounded `ask` loop, and JSONL audit transcripts with replay and generation
  receipts.
- Tools: arXiv search, web search, sandboxed file read/write.
- Role-scoped tool sets (market, academic, reader, writer), `Agent` sugar with typed
  agent-to-agent handoff, and `examples/Multiagent.lean`.
- Model reasoning (OpenAI `reasoning_content`, Anthropic thinking blocks) is
  captured as an audit-only event, never fed back to the model.

### Fixed
- `Arxiv.urlEncode` is total. The real HTTP status is recovered from curl and
  retries are classified on it (429/5xx retry, 4xx fatal).
