module

public import LeanAgent.Retry
public meta import LeanAgent.Retry

namespace LeanAgent

public section

/-- Result of one bounded attempt: either continue with updated state, or finish
with an outcome. `σ` is the loop state carried between attempts (e.g. the message
history plus accumulated events); `ω` is the terminal result (e.g. a `Transcript`
or an `Except ExtractError α`). -/
public inductive Progress (σ ω : Type) where
  | more (state : σ)
  | done (outcome : ω)
  deriving Inhabited

/-- Bounded retry driver shared by `extract`, `extractAudited`, and `askWith`.

Runs `step attempt state` for `attempt = 0 .. maxAttempts-1`, threading the state.
`.done ω` stops early and returns `ω`; `.more σ'` carries the new state to the
next attempt. If every attempt returns `.more`, `exhausted` maps the final state
to a terminal outcome (the "ran out of attempts" case each caller shapes itself).

The caller owns the `maxAttempts == 0` and any pre-flight guards, because each
call site produces a different refusal value; this driver only owns the loop
bound and the exhaustion fallthrough — the parts that were previously duplicated
and easy to desynchronize. -/
public def runBounded {σ ω : Type} (maxAttempts : Nat)
    (step : Nat → σ → IO (Progress σ ω)) (init : σ) (exhausted : σ → ω) : IO ω := do
  let mut state := init
  for attempt in *...maxAttempts do
    match ← step attempt state with
    | .more state' => state := state'
    | .done outcome => return outcome
  return exhausted state

/-- Retry decision reused across the loops: retryable transport, and not the
final attempt. Keys off the typed HTTP error so classification uses the numeric
status directly. -/
public def shouldRetryPost (e : HttpError) (attempt maxAttempts : Nat) : Bool :=
  classifyHttp e == .retryable && attempt + 1 < maxAttempts

/-- Backoff between retryable attempts. `baseMs` doubles each attempt up to
`maxMs`; `jitterMs` adds a bounded pseudo-random spread so many clients don't
retry in lockstep. `sleep := none` disables waiting (tests stay instant). -/
public structure BackoffPolicy where
  baseMs : Nat := 250
  maxMs : Nat := 8000
  jitterMs : Nat := 100
  /-- Injected sleeper; `none` means do not sleep (deterministic tests). Live
  code supplies `some (IO.sleep ·.toUInt32)`. -/
  sleep : Option (Nat → IO Unit) := some (fun ms => IO.sleep ms.toUInt32)

/-- A backoff policy that never sleeps — for deterministic, instant tests. -/
public def BackoffPolicy.noSleep : BackoffPolicy := { sleep := Option.none }

/-- Exponential delay for a 0-indexed attempt: `min maxMs (baseMs * 2^attempt)`
plus a deterministic jitter derived from the attempt. Pure, so it is testable. -/
public def BackoffPolicy.delayMs (p : BackoffPolicy) (attempt : Nat) : Nat :=
  let raw := p.baseMs * (2 ^ attempt)
  let capped := min p.maxMs raw
  let jitter := if p.jitterMs == 0 then 0 else (attempt * 2654435761) % (p.jitterMs + 1)
  capped + jitter

/-- Wait before a retry, if the policy provides a sleeper. -/
public def BackoffPolicy.wait (p : BackoffPolicy) (attempt : Nat) : IO Unit :=
  match p.sleep with
  | some s => s (p.delayMs attempt)
  | none => pure ()

#guard (BackoffPolicy.delayMs { jitterMs := 0 } 0) == 250
#guard (BackoffPolicy.delayMs { jitterMs := 0 } 1) == 500
#guard (BackoffPolicy.delayMs { jitterMs := 0 } 2) == 1000
#guard (BackoffPolicy.delayMs { baseMs := 250, maxMs := 800, jitterMs := 0 } 5) == 800  -- capped

/-- Whether `attempt` (0-indexed) is the last one under `maxAttempts`. -/
public def isLastAttempt (attempt maxAttempts : Nat) : Bool :=
  attempt + 1 == maxAttempts

#guard shouldRetryPost { status? := some 429, body := "" } 0 3 == true
#guard shouldRetryPost { status? := some 429, body := "" } 2 3 == false  -- last attempt: no retry
#guard shouldRetryPost { status? := some 401, body := "" } 0 3 == false  -- fatal: no retry
#guard isLastAttempt 2 3 == true
#guard isLastAttempt 0 3 == false

/-- Pure driver over the identity monad, used only to unit-test `runBounded`'s
control flow (early `.done`, exhaustion, zero attempts) at compile time. -/
private def runBoundedId {σ ω : Type} (maxAttempts : Nat)
    (step : Nat → σ → Progress σ ω) (init : σ) (exhausted : σ → ω) : ω := Id.run do
  let mut state := init
  for attempt in *...maxAttempts do
    match step attempt state with
    | .more state' => state := state'
    | .done outcome => return outcome
  return exhausted state

-- Stops early on `.done`.
#guard
  runBoundedId (σ := Nat) (ω := Nat) 5
    (fun attempt s => if attempt == 2 then .done s else .more (s + 1)) 0 (· + 100) == 2

-- Exhaustion path when every attempt says `.more`.
#guard
  runBoundedId (σ := Nat) (ω := Nat) 3 (fun _ s => .more (s + 1)) 0 (· + 100) == 103

-- Zero attempts: `step` runs zero times, exhaustion path with the initial state.
#guard
  runBoundedId (σ := Nat) (ω := Nat) 0 (fun _ _ => .done 999) 7 id == 7

end

end LeanAgent
