module

public import LeanAgent.Util
public import LeanAgent.Types
public import LeanAgent.Transport

namespace LeanAgent.Curl

open LeanAgent

public section

/-- Sentinel that `-w` appends to stdout so we can recover the real HTTP status
even when `--fail-with-body` also prints the error body. Never appears in a
provider payload. -/
public def statusSentinel : String := "\n__lean_agent_http__:"

/-- `-w` writes the response status after the body, tagged with `statusSentinel`. -/
public def writeOut : String := statusSentinel ++ "%{http_code}"

/-- `curl` argv. The bearer token is never an argument; it lives in `@headerFile` if at all. -/
public def argv (url : String) (headerFile? : Option System.FilePath) : Array String :=
  let auth :=
    match headerFile? with
    | some path => #["-H", s!"@{path}"]
    | none => #[]
  #["-sS", "--fail-with-body", "-m", "120", "-w", writeOut, "-X", "POST", url,
    "-H", "Content-Type: application/json"] ++
    auth ++
    #["--data-binary", "@-"]

public def getArgv (url : String) : Array String :=
  #["-sS", "--fail-with-body", "-m", "60", "-w", writeOut,
    "-A", "lean-agent/0.1 (arxiv_search)", url]

public def argvContains (args : Array String) (needle : String) : Bool :=
  args.any (fun a => a.contains needle)

/-- Split the `-w` status sentinel off the tail of curl stdout.
Returns the body with the sentinel removed and the parsed HTTP status, if any. -/
public def splitStatus (raw : String) : String × Option Nat :=
  match (raw.splitOn statusSentinel).reverse with
  | [] => (raw, none)
  | [_only] => (raw, none)
  | codeStr :: bodyRev =>
    let body := joinSep statusSentinel bodyRev.reverse
    let trimmed := (codeStr.dropWhile Char.isWhitespace).dropEndWhile Char.isWhitespace
    (body, trimmed.toString.toNat?)

/-- Curl diagnostics for a failed process (stderr, or a synthetic exit note). -/
public def diag (out : IO.Process.Output) : String :=
  if nonemptyText out.stderr then out.stderr else ""

/-- Build a typed `HttpError` from a nonzero-exit curl process. When curl
recovered an HTTP status via `-w`, it is a server-answered error (`status?`);
otherwise the request never completed and curl's exit code is the signal. -/
public def toError (out : IO.Process.Output) (code? : Option Nat) (body : String) : HttpError :=
  let note := diag out
  let combinedBody :=
    if nonemptyText note && nonemptyText body then note ++ "\n" ++ body
    else if nonemptyText note then note
    else body
  match code? with
  | some _ => { status? := code?, body := combinedBody }
  | none => { curlExit? := some out.exitCode.toNat, body := combinedBody }

public def get (url : String) : IO HttpResult := do
  let out ← IO.Process.output { cmd := "curl", args := getArgv url }
  let (body, code?) := splitStatus out.stdout
  if out.exitCode == 0 then
    pure (.ok (code?.getD 200) body)
  else
    pure (.err (toError out code? body))

public def postWithHeader (url body : String) (headerFile? : Option System.FilePath) :
    IO HttpResult := do
  let out ← IO.Process.output {
    cmd := "curl"
    args := argv url headerFile?
  } (input? := some body)
  let (respBody, code?) := splitStatus out.stdout
  if out.exitCode == 0 then
    pure (.ok (code?.getD 200) respBody)
  else
    pure (.err (toError out code? respBody))

/-- A missing API-key env var, surfaced as a typed error (not a completed request). -/
public def missingEnvError (name : String) : HttpResult :=
  .err { body := s!"missing environment variable `{name}`" }

/-- POST JSON on stdin. Header content depends on `AuthHeader`; secret values never appear in argv. -/
public def post (url body : String) (auth : AuthHeader) : IO HttpResult := do
  match auth with
  | .none => postWithHeader url body none
  | .bearer name =>
    match ← IO.getEnv name with
    | none => pure (missingEnvError name)
    | some token =>
      IO.FS.withTempFile fun handle path => do
        handle.putStr s!"Authorization: Bearer {token}\n"
        handle.flush
        postWithHeader url body (some path)
  | .anthropic name =>
    match ← IO.getEnv name with
    | none => pure (missingEnvError name)
    | some token =>
      IO.FS.withTempFile fun handle path => do
        handle.putStr s!"x-api-key: {token}\nanthropic-version: 2023-06-01\n"
        handle.flush
        postWithHeader url body (some path)

#guard
  let (body, code?) := splitStatus ("{\"ok\":true}" ++ statusSentinel ++ "200")
  body == "{\"ok\":true}" && code? == some 200

#guard
  let (body, code?) := splitStatus ("{\"error\":\"nope\"}" ++ statusSentinel ++ "429")
  body == "{\"error\":\"nope\"}" && code? == some 429

#guard
  let (body, code?) := splitStatus "no sentinel here"
  body == "no sentinel here" && code?.isNone

#guard argvContains (argv "https://x" none) "%{http_code}"
#guard !argvContains (argv "https://x" none) "Bearer"

end

end LeanAgent.Curl
