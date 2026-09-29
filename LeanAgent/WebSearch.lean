module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Json
public import LeanAgent.Curl
public meta import LeanAgent.Json
public meta import LeanAgent.Curl

namespace LeanAgent.Web

open Lean
open LeanAgent

public section

/-- One web result: a title/heading, a URL, and a short text snippet. -/
public structure Hit where
  title : String
  url : String
  snippet : String
  deriving Repr, BEq

/-- Percent-encode a query for a URL query string. Total: folds over UTF-8 bytes. -/
public def urlEncode (s : String) : String :=
  let hex2 (n : Nat) : String :=
    let d (x : Nat) : Char :=
      if x < 10 then Char.ofNat ('0'.toNat + x)
      else Char.ofNat ('A'.toNat + (x - 10))
    let v := n % 256
    String.ofList [d (v / 16), d (v % 16)]
  s.foldl (init := "") fun acc c =>
    if c.isAlphanum || c == '-' || c == '_' || c == '.' then acc.push c
    else if c == ' ' then acc ++ "%20"
    else (String.singleton c).toUTF8.foldl (init := acc) fun out b => out ++ "%" ++ hex2 b.toNat

/-- DuckDuckGo Instant Answer API: JSON, no key required. Not a full web index,
but dependency-free and good enough for a demo tool. -/
public def queryUrl (query : String) : String :=
  "https://api.duckduckgo.com/?format=json&no_html=1&skip_disambig=1&q=" ++ urlEncode query

private def strOf (j : Json) (key : String) : String :=
  match j.getObjVal? key with
  | .ok v => match v.getStr? with | .ok s => s | .error _ => ""
  | .error _ => ""

/-- Flatten a DuckDuckGo `RelatedTopics` node (which may itself nest `Topics`). -/
private partial def topicHits (j : Json) : Array Hit :=
  match j.getObjVal? "Topics" with
  | .ok sub =>
    match sub.getArr? with
    | .ok arr => arr.foldl (init := #[]) fun acc t => acc ++ topicHits t
    | .error _ => #[]
  | .error _ =>
    let text := strOf j "Text"
    let url := strOf j "FirstURL"
    if nonemptyText text && nonemptyText url then
      -- Title is the leading segment of Text before " - ", when present.
      let title :=
        match (text.splitOn " - ") with
        | first :: _ :: _ => first
        | _ => text
      #[{ title, url, snippet := text }]
    else #[]

/-- Parse a DuckDuckGo Instant Answer JSON body into hits. Pure; fail-soft:
a malformed body yields no hits rather than an error (search is best-effort). -/
public def parseResults (raw : String) : Array Hit :=
  match Json.parse raw with
  | .error _ => #[]
  | .ok j =>
    let abstractHit : Array Hit :=
      let text := strOf j "AbstractText"
      let url := strOf j "AbstractURL"
      let heading := strOf j "Heading"
      if nonemptyText text && nonemptyText url then
        #[{ title := if nonemptyText heading then heading else text, url, snippet := text }]
      else #[]
    let related : Array Hit :=
      match j.getObjVal? "RelatedTopics" with
      | .ok rt =>
        match rt.getArr? with
        | .ok arr => arr.foldl (init := #[]) fun acc t => acc ++ topicHits t
        | .error _ => #[]
      | .error _ => #[]
    abstractHit ++ related

public def formatHits (hits : Array Hit) (maxHits : Nat := 5) : String :=
  if hits.isEmpty then "no web results"
  else
    joinSep "\n\n" ((hits.toList.take maxHits).map fun h =>
      let snip := (h.snippet.take 280).toString
      h.title ++ "\n" ++ h.url ++ "\n" ++ snip)

/-- Live web search. Best-effort: transport failures return a readable string
(recorded as a tool result), never an exception. -/
public def search (query : String) : IO String := do
  if !nonemptyText query then
    return "web_search: blank query"
  match ← Curl.get (queryUrl query) with
  | .err e => pure s!"web_search transport: {e.detail}"
  | .ok _status raw => pure (formatHits (parseResults raw))

#guard urlEncode "market size 2026" == "market%20size%202026"

#guard
  let raw := "{\"Heading\":\"Lean (proof assistant)\",\"AbstractText\":\"Lean is a theorem prover.\",\"AbstractURL\":\"https://example.com/lean\",\"RelatedTopics\":[]}"
  match (parseResults raw)[0]? with
  | some h => h.title == "Lean (proof assistant)" && h.url.contains "example.com"
  | none => false

#guard
  let raw := "{\"AbstractText\":\"\",\"AbstractURL\":\"\",\"RelatedTopics\":[{\"Text\":\"Widget market - overview\",\"FirstURL\":\"https://example.com/widgets\"}]}"
  match (parseResults raw)[0]? with
  | some h => h.title == "Widget market" && h.snippet.contains "overview"
  | none => false

#guard (parseResults "not json").isEmpty

end

end LeanAgent.Web
