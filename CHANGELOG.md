# Changelog

All notable changes to **lean-agent** are documented here. The format follows
[Keep a Changelog](https://keepachangelog.com/en/1.1.0/), and the project adheres to
[Semantic Versioning](https://semver.org/spec/v2.0.0.html).

Unless noted otherwise, every release builds clean (`lake build`) and passes the
suite (`lake test`), with no `sorry` and no `native_decide`. From the release after
0.1.1, `lake check --paranoid` accepts the library with only the three standard
axioms (`propext`, `Quot.sound`, `Classical.choice`).

## [Unreleased]

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
