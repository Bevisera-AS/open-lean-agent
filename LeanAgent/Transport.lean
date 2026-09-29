module

public import LeanAgent.Util
public meta import LeanAgent.Util

namespace LeanAgent

public section

/-- Token accounting for one model call. Fields are optional because not every
provider returns every count (Anthropic reports input/output, not a total; some
local servers report nothing). -/
public structure Usage where
  promptTokens : Option Nat := none
  completionTokens : Option Nat := none
  totalTokens : Option Nat := none
  deriving Repr, BEq, Inhabited

public def Usage.empty : Usage := {}

/-- True when the usage record carries no counts at all. -/
public def Usage.isEmpty (u : Usage) : Bool :=
  u.promptTokens.isNone && u.completionTokens.isNone && u.totalTokens.isNone

/-- Add two optional counts, treating absence as zero only when the other side is
present, so summing over turns keeps `none` iff neither turn reported a count. -/
private def addOpt (a b : Option Nat) : Option Nat :=
  match a, b with
  | none, none => none
  | some x, none => some x
  | none, some y => some y
  | some x, some y => some (x + y)

/-- Accumulate usage across turns of a multi-call run (e.g. tool loops). -/
public def Usage.add (a b : Usage) : Usage :=
  { promptTokens := addOpt a.promptTokens b.promptTokens
    completionTokens := addOpt a.completionTokens b.completionTokens
    totalTokens := addOpt a.totalTokens b.totalTokens }

#guard
  (Usage.add { promptTokens := some 3 } { promptTokens := some 4, totalTokens := some 4 })
    == { promptTokens := some 7, totalTokens := some 4 }

/-- A failed HTTP attempt. `status?` is the numeric HTTP code when the server
answered (recovered from curl's `-w`); `curlExit?` is curl's process exit code
when the request never completed (timeout, DNS, connection). `body` is the
response body or curl diagnostics. No secrets. -/
public structure HttpError where
  status? : Option Nat := none
  curlExit? : Option Nat := none
  body : String
  deriving Repr, BEq, Inhabited

/-- Result of one HTTP attempt: a 2xx-ish success with numeric status and body,
or a typed error. Replaces the old `Except String String` transport seam so the
HTTP status survives as a number instead of being stringified and re-parsed. -/
public inductive HttpResult where
  | ok (status : Nat) (body : String)
  | err (error : HttpError)
  deriving Repr, BEq, Inhabited

/-- Human-readable detail for logs and transcripts. Keeps a leading `http <code>`
token when a status is known, so any string-based inspection (e.g. matching a
provider error body) still finds it. No secrets. -/
public def HttpError.detail (e : HttpError) : String :=
  let statusTok :=
    match e.status? with
    | some code => s!"http {code} "
    | none => ""
  let exitTok :=
    match e.curlExit? with
    | some code => s!"curl exit {code} "
    | none => ""
  let tokens := statusTok ++ exitTok
  if nonemptyText e.body then tokens ++ e.body else tokens.trimAscii.copy

/-- The success body, if any. -/
public def HttpResult.body? : HttpResult → Option String
  | .ok _ body => some body
  | .err _ => none

#guard (HttpError.detail { status? := some 429, body := "{\"error\":\"slow\"}" }).startsWith "http 429 "
#guard (HttpError.detail { curlExit? := some 28, body := "timeout" }).startsWith "curl exit 28 "
#guard HttpError.detail { body := "raw" } == "raw"
#guard Usage.isEmpty Usage.empty
#guard !Usage.isEmpty { totalTokens := some 42 }

end

end LeanAgent
