# `lake check --paranoid` report

Lean 4.35.0 (2026-10-15) ships `lake check`. It exports a development and replays it
through Lean's kernel, rejecting any non-standard axiom. With `--paranoid` it also runs
every external checker bundled with Lean: a hardened-allocator build of Lean's own
kernel (`leanchecker-paranoid`), lean4lean, nanoda, and the verified kernels
con-leche (proven consistent in Lean) and con-ron (a Rust refinement of con-leche).
Background: [Lean now ships with verified kernels](https://leodemoura.github.io/blog/2026-10-15-lean-now-ships-with-verified-kernels/).

This report covers the runs on lean-agent on 2026-10-16, after moving the toolchain
from Lean 4.33.0 to 4.35.0.

## Result

| Checker | Result |
|---|---|
| Lean default kernel | accepts |
| Lean paranoid kernel | accepts |
| lean4lean | accepts (67,092 declarations) |
| nanoda | accepts |
| con-leche | accepts (67,095 declarations, `--verified`) |
| con-ron | accepts (67,095 declarations, `--verified`) |
| Axiom policy | passes: `propext`, `Quot.sound`, `Classical.choice` |

The run covers the default target, the whole `LeanAgent` library (31 modules), with
the sandbox on, on Linux, in the CI image (`ci/Dockerfile`). `lake check` exits 0.
The run took about 4 minutes.

The upgrade itself needed no source changes: `lake build` is warning-free and
`lake test` passes on 4.35.0.

nanoda logs `Skipped exported but unpermitted axioms ["sorryAx"]`. That axiom is
declared in Lean's core and so is always exported; nothing in lean-agent uses it. It
is absent from the axioms reported above, and there is no `sorry` in the sources.

## What this does and does not establish

At the time of the run, lean-agent had one theorem (`GenerationReceipt.ofTranscript_sound`,
five `rfl`s); its checks were 154 compile-time `#guard`s plus the `lean-agent-tests`
binary. So `lake check` here establishes that:

- every definition, instance and derived declaration in the library is
  type-correct, independently re-checked by six kernels, two of them verified;
- the library depends on no axiom beyond the standard three, so there is no
  `native_decide` and no `sorry`.

It does **not** re-check the `#guard`s. A `#guard` is evaluated by Lean's
interpreter when the module elaborates; its result is not stored in the exported
environment, so no kernel sees it. The guards and the test binary remain checked by
`lake build` and `lake test`, which trust Lean's compiler.

Since the run, the decidable checks have been restated as theorems, proved `by
decide` (or `by decide +kernel` where the statement folds over arrays or tree
maps): the lexical path rule in `LeanAgent/Files.lean`, and in
`LeanAgent/Theorems.lean` fail-closed field decoding, off-catalog tool refusal,
the fixture contract's round trip and echo replay against a tampered result. A
theorem's proof term is in the exported environment, so these are under `lake
check` on the next CI run; they were not part of the run above. What it took,
on this toolchain:

- `String.any`, `String.all`, `String.splitOn` and `Array.all` do not reduce
  under `decide`; `nonemptyText`, `safeRunId` and `safeRelPath` are now stated
  over `List Char`, with `@[expose]` so an importing module can unfold them.
- Inside a `module` file, `decide` cannot unfold `Lean.Data.Json` (not exposed
  by Lean), so `Theorems.lean` is deliberately a legacy (non-`module`) file:
  a legacy import sees every body. The library glob builds it like any module.
- `#print axioms` on each theorem reports only `propext`, `Classical.choice` and
  `Quot.sound`.

Those `decide` theorems check one input each. The quantified statements came
after them and are proved by case analysis, not reduction, so they do not depend
on what `decide` can unfold and live in the `module` files next to their
decoders: `mkToolSet_decode_declared` (`LeanAgent/ToolDSL.lean`),
`decodeDemoTool_ok_name` (`LeanAgent/Tools.lean`), `decodeRunKind_ok`,
`decodeEventWith_ok_tag` and `decodeStop_ok_reason`
(`LeanAgent/Transcript.lean`). They too are under `lake check` on the next CI
run and were not part of the run above.

## Setup findings

These shaped how the check is run; none is a defect in lean-agent.

1. **Executables were the default target. Fixed.** The default target used to be the
   `lean-agent` executable, so the first run only checked what `LeanAgentQuery`
   imports (66,796 declarations). `lake check` imports every default target into one
   environment, and the three executables each define `main`, so they cannot all be
   default targets. The `LeanAgent` library is now the only default target; the
   executables build by name: `lake build lean-agent lean-agent-tests multiagent`.
   The test driver `LeanAgentTests.lean` defines `main` and so stays out of the
   check.
2. **The sandbox needs Linux user namespaces.** `lake check` sandboxes the build with
   `bwrap` and refuses to run on macOS. In Docker, the run above used
   `--security-opt seccomp=unconfined --security-opt apparmor=unconfined
   --security-opt systempaths=unconfined` (without `systempaths=unconfined`, `bwrap`
   cannot mount `/proc`); `--privileged` also works. On GitLab that means a runner
   that starts job containers privileged (GitLab.com's shared runners do). On
   GitHub's `ubuntu-24.04` runners the workflow first sets
   `kernel.apparmor_restrict_unprivileged_userns=0`.
3. **`bwrap` needs `/run/user` to exist.** In a slim image it fails with
   `Can't mkdir /run/user: Read-only file system`. The CI image creates it, and the
   GitLab job does too.
4. **The toolchain must live outside the project.** Learned on lean-spec: with
   `ELAN_HOME` under the project directory `lake check` stalls at "Resolving
   dependencies". The GitLab `kernel-check` job installs to `/opt/elan` and skips the
   cache.

## Reproduce

On Linux, with user namespaces available:

```sh
lake check --paranoid
```

Locally on any machine with Docker, using the CI image:

```sh
docker build --build-arg LEAN_TOOLCHAIN="$(cat lean-toolchain)" -t lean-agent-ci ci
docker run --rm --privileged -v "$PWD":/src:ro lean-agent-ci \
  sh -c 'cp -r /src /work/p && cd /work/p && rm -rf .lake && lake check --paranoid'
```

The copy keeps a macOS `.lake` (the wrong platform's binaries) out of the run.

## In CI

`.gitlab-ci.yml` has a `kernel-check` job that runs `lake check --paranoid`,
sandboxed, on merge requests, on the default branch, on tags and on "Run pipeline"
from the GitLab UI. It keeps the log as an artifact. The GitHub mirror of
open-lean-agent runs the same check in `.github/workflows/ci.yml`. Neither ever
passes `--inadvisably-no-sandbox`.
