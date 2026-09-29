module

public import Lean.Data.Json
public import LeanAgent.Types
public import LeanAgent.Transport
public import LeanAgent.OutputContract
public import LeanAgent.Json
public meta import LeanAgent.Types
public meta import LeanAgent.Transport
public meta import LeanAgent.OutputContract
public meta import LeanAgent.Json

namespace LeanAgent

open Lean

public section

/-- Whether a failed post or extract may be attempted again. Decode repair is
retryable until `maxAttempts`. Truncation and schema refusal after the bound
are fatal. -/
public inductive FailureClass where
  | retryable
  | fatal
  deriving Repr, BEq, DecidableEq

/-- Bound on model calls. `0` refuses without posting. Default matches Instructor-style retry. -/
public structure ExtractPolicy where
  maxAttempts : Nat := 3
  deriving Repr, BEq

public def repairMessage (hint : String) : Message := {
  role := .user
  content := hint
}

public def appendRepair (msgs : Array Message) (assistantContent? : Option String)
    (hint : String) : Array Message :=
  let withAssistant :=
    match assistantContent? with
    | some content => msgs.push { role := .assistant, content }
    | none => msgs
  withAssistant.push (repairMessage hint)

/-- OpenAI `error.type`/`error.code` or Anthropic `error.type`. -/
public def decodeApiError (raw : String) : Option (String × String) :=
  match Json.parse raw with
  | .error _ => none
  | .ok j =>
    match j.getObjVal? "error" with
    | .error _ => none
    | .ok err =>
      let code? :=
        match err.getObjVal? "type" with
        | .ok t =>
          match t.getStr? with
          | .ok s => some s
          | .error _ => none
        | .error _ =>
          match err.getObjVal? "code" with
          | .ok c =>
            match c.getStr? with
            | .ok s => some s
            | .error _ => none
          | .error _ => none
      let msg? :=
        match err.getObjVal? "message" with
        | .ok m =>
          match m.getStr? with
          | .ok s => some s
          | .error _ => none
        | .error _ => none
      match code?, msg? with
      | some code, some msg => some (code, msg)
      | some code, none => some (code, "")
      | none, some msg => some ("error", msg)
      | none, none => none

public def classifyApiCode (code : String) : FailureClass :=
  match code with
  | "rate_limit_error" | "overloaded_error" | "rate_limit_exceeded" => .retryable
  | _ => .fatal

/-- Recover a `http <code>` status token that `Curl.failDetail` prepends. -/
public def httpStatusOf (detail : String) : Option Nat :=
  if detail.startsWith "http " then
    let rest := (detail.drop 5).dropWhile Char.isWhitespace
    let digits := rest.takeWhile Char.isDigit
    digits.toString.toNat?
  else
    none

/-- HTTP status codes that warrant a retry: rate limiting and transient 5xx. -/
public def retryableStatus (code : Nat) : Bool :=
  code == 429 || (code >= 500 && code <= 599)

/-- Network-level curl exit signatures (timeout, connect, DNS, reset) are transient. -/
public def transientNetwork (detail : String) : Bool :=
  detail.contains "Operation timed out" ||
    detail.contains "timed out" ||
    detail.contains "Connection reset" ||
    detail.contains "Could not resolve host" ||
    detail.contains "Failed to connect" ||
    detail.contains "Connection refused"

/-- Classify a failed POST body. Prefer the real HTTP status recovered from the
`-w` sentinel; fall back to the API error object, then to transient-network
signatures. Authentication and other 4xx are fatal. -/
public def classifyPostFailure (detail : String) : FailureClass :=
  match httpStatusOf detail with
  | some code => if retryableStatus code then .retryable else .fatal
  | none =>
    match decodeApiError detail with
    | some (code, _) => classifyApiCode code
    | none => if transientNetwork detail then .retryable else .fatal

/-- Classify a typed HTTP error. Uses the numeric status directly when present
(no string round-trip), then the provider error object in the body, then curl
exit / transient-network signatures. Authentication and other 4xx are fatal. -/
public def classifyHttp (e : HttpError) : FailureClass :=
  match e.status? with
  | some code => if retryableStatus code then .retryable else .fatal
  | none =>
    match decodeApiError e.body with
    | some (code, _) => classifyApiCode code
    | none => if transientNetwork e.detail then .retryable else .fatal

/-- Recover a provider `(code, message)` from a typed error's body, if it carries
a provider error object. -/
public def HttpError.provider? (e : HttpError) : Option (String × String) :=
  decodeApiError e.body

public def ExtractError.classify : ExtractError → FailureClass
  | .transport d => classifyPostFailure d
  | .refused _ _ => .fatal
  | .truncated => .fatal
  | .provider code _ => classifyApiCode code

#guard classifyHttp { status? := some 429, body := "" } == FailureClass.retryable
#guard classifyHttp { status? := some 401, body := "" } == FailureClass.fatal
#guard
  classifyHttp { body := "{\"error\":{\"type\":\"overloaded_error\",\"message\":\"x\"}}" }
    == FailureClass.retryable
#guard classifyHttp { curlExit? := some 28, body := "Operation timed out" } == FailureClass.retryable
#guard classifyHttp { curlExit? := some 6, body := "Could not resolve host" } == FailureClass.retryable
#guard classifyHttp { body := "totally unknown" } == FailureClass.fatal

#guard
  match decodeApiError "{\"error\":{\"type\":\"invalid_request_error\",\"message\":\"bad schema\"}}" with
  | some ("invalid_request_error", "bad schema") => true
  | _ => false

#guard
  match decodeApiError "{\"type\":\"error\",\"error\":{\"type\":\"rate_limit_error\",\"message\":\"slow down\"}}" with
  | some ("rate_limit_error", "slow down") => true
  | _ => false

#guard classifyApiCode "rate_limit_error" == FailureClass.retryable
#guard classifyApiCode "authentication_error" == FailureClass.fatal
#guard httpStatusOf "http 429 curl exit 22\n{...}" == some 429
#guard httpStatusOf "connection refused" == none
#guard retryableStatus 429 && retryableStatus 503 && !retryableStatus 401
-- Real status recovered from the `-w` sentinel drives the decision.
#guard classifyPostFailure "http 429 curl: (22)\n{\"error\":\"slow\"}" == FailureClass.retryable
#guard classifyPostFailure "http 503 curl: (22)" == FailureClass.retryable
#guard classifyPostFailure "http 401 curl: (22)\n{\"error\":\"bad key\"}" == FailureClass.fatal
#guard classifyPostFailure "http 404 curl: (22)" == FailureClass.fatal
-- No status token: fall back to API error object, then transient-network signatures.
#guard classifyPostFailure "curl: (7) Failed to connect to host" == FailureClass.retryable
#guard classifyPostFailure "curl: (7) Connection refused" == FailureClass.retryable
#guard classifyPostFailure "curl: (28) Operation timed out" == FailureClass.retryable
#guard classifyPostFailure "some other fatal error" == FailureClass.fatal
#guard ExtractError.classify .truncated == FailureClass.fatal
#guard
  ExtractError.classify (.provider "overloaded_error" "try later") == FailureClass.retryable

#guard
  let err : DecodeError := .unknownFields "requirement" ["oops"]
  (repairMessage (defaultRepairHint "requirement" err)).content.contains "unknown fields oops"

#guard
  let err : DecodeError := .missingField "requirement" "strength"
  let msgs := appendRepair #[{ role := .user, content := "specify" }] (some "{}")
    (defaultRepairHint "requirement" err)
  msgs.size == 3 &&
    (match msgs[2]? with
     | some m => m.role == .user && m.content.contains "missing field `strength`"
     | none => false)

end

end LeanAgent
