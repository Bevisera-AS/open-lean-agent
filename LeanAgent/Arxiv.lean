module

public import LeanAgent.Util
public import LeanAgent.Curl
public meta import LeanAgent.Curl

namespace LeanAgent.Arxiv

open LeanAgent

public section

public structure Hit where
  id : String
  title : String
  summary : String
  deriving Repr, BEq

public def hex2 (n : Nat) : String :=
  let d (x : Nat) : Char :=
    if x < 10 then Char.ofNat ('0'.toNat + x)
    else Char.ofNat ('A'.toNat + (x - 10))
  let v := n % 256
  String.ofList [d (v / 16), d (v % 16)]

public def urlEncode (s : String) : String :=
  s.foldl (init := "") fun acc c =>
    if c.isAlphanum || c == '-' || c == '_' || c == '.' then
      acc.push c
    else if c == ' ' then
      acc.push '+'
    else
      let bytes := (String.singleton c).toUTF8
      bytes.foldl (init := acc) fun out b => out ++ "%" ++ hex2 b.toNat

public def queryUrl (query : String) (maxResults : Nat := 5) : String :=
  "https://export.arxiv.org/api/query?search_query=all:" ++
    urlEncode query ++
    "&start=0&max_results=" ++ toString maxResults

public def stripSpace (s : String) : String :=
  (s.dropWhile Char.isWhitespace |>.dropEndWhile Char.isWhitespace).toString

public def firstBetween (hay openTag closeTag : String) : Option String :=
  match hay.splitOn openTag with
  | [] | [_] => none
  | _ :: rest =>
    let after := joinSep openTag rest
    match after.splitOn closeTag with
    | [] => none
    | inner :: closeRest =>
      if closeRest.isEmpty then none else some (stripSpace inner)

public def parseEntries (xml : String) : Array Hit :=
  let chunks := (xml.splitOn "<entry>").drop 1
  chunks.foldl (init := #[]) fun acc chunk =>
    match firstBetween chunk "<title>" "</title>", firstBetween chunk "<id>" "</id>" with
    | some title, some id =>
      let summary := (firstBetween chunk "<summary>" "</summary>").getD ""
      acc.push { id, title, summary }
    | _, _ => acc

public def formatHits (hits : Array Hit) : String :=
  if hits.isEmpty then
    "no arXiv hits"
  else
    joinSep "\n\n" (hits.toList.map fun h =>
      let sum := (h.summary.take 280).toString
      h.id ++ "\n" ++ h.title ++ "\n" ++ sum)

public def search (query : String) : IO String := do
  if !nonemptyText query then
    return "arxiv_search: blank query"
  match ← Curl.get (queryUrl query) with
  | .err e => pure s!"arxiv_search transport: {e.detail}"
  | .ok _status xml => pure (formatHits (parseEntries xml))

#guard urlEncode "lean 4" == "lean+4"
#guard urlEncode "λ" == "%CE%BB"
#guard
  let xml :=
    "<feed><title>feed</title><entry><id>http://arxiv.org/abs/2401.00001</id>" ++
      "<title>Lean Demo</title><summary>A paper.</summary></entry></feed>"
  match (parseEntries xml)[0]? with
  | some h => h.title == "Lean Demo" && h.id.contains "2401.00001"
  | none => false

end

end LeanAgent.Arxiv
