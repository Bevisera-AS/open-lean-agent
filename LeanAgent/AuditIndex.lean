module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Json
public import LeanAgent.Transcript
public meta import LeanAgent.Json
public meta import LeanAgent.Transcript

/-!
A rebuildable, append-only index over the audit directory. Each run's full
transcript stays the source of truth (one `<runId>.jsonl` per run); the index is
a derived manifest (`index.jsonl`, one `AuditEntry` per line) so consumers can
answer "which refused runs on bedrock, and how many tokens" without decoding
every transcript. The index can always be rebuilt from the transcripts.
-/

namespace LeanAgent

open Lean

public section

/-- One row of the audit manifest: run metadata projected from a transcript,
plus where its full transcript lives. Derived and rebuildable. -/
public structure AuditEntry where
  runId : String
  kind : RunKind
  providerId : String
  model : String
  stop : StopReason
  usage : Usage := {}
  file : String
  promptPreview : String := ""
  deriving Repr, BEq

/-- Manifest file name inside the audit directory. Excluded when scanning
transcripts so the index never indexes itself. -/
public def indexFileName : String := "index.jsonl"

/-- First 120 chars of the prompt, whitespace-trimmed, for a readable manifest. -/
public def previewOf (prompt : String) : String :=
  (prompt.take 120).toString

public def AuditEntry.ofTranscriptWith {Tool : Type} (file : String)
    (t : Transcript Tool) : AuditEntry :=
  { runId := t.runId, kind := t.kind, providerId := t.providerId, model := t.model
    stop := t.stop, usage := t.usage, file, promptPreview := previewOf t.prompt }

private def natOr (n? : Option Nat) : Json :=
  match n? with | some n => (n : Json) | none => Json.null

public def encodeAuditEntry (e : AuditEntry) : Json :=
  Json.mkObj [
    ("runId", Json.str e.runId),
    ("kind", Json.str e.kind.toWire),
    ("providerId", Json.str e.providerId),
    ("model", Json.str e.model),
    ("stop", encodeStop e.stop),
    ("usage", Json.mkObj [
      ("promptTokens", natOr e.usage.promptTokens),
      ("completionTokens", natOr e.usage.completionTokens),
      ("totalTokens", natOr e.usage.totalTokens)
    ]),
    ("file", Json.str e.file),
    ("promptPreview", Json.str e.promptPreview)
  ]

private def usageNat (j : Json) (key : String) : Option Nat :=
  match j.getObjVal? key with
  | .error _ => none
  | .ok v => match v.getNat? with | .ok n => some n | .error _ => none

public def decodeAuditEntry (j : Json) : Except DecodeError AuditEntry := do
  let o ← asObj "auditEntry" j
  exactFields "auditEntry"
    ["runId", "kind", "providerId", "model", "stop", "usage", "file", "promptPreview"] o
  let runId ← strField "auditEntry" "runId" j
  let kind ← decodeRunKind (← strField "auditEntry" "kind" j)
  let providerId ← strField "auditEntry" "providerId" j
  let model ← strField "auditEntry" "model" j
  let stop ← decodeStop (← field "auditEntry" "stop" j)
  let usageJ ← field "auditEntry" "usage" j
  let usage : Usage :=
    { promptTokens := usageNat usageJ "promptTokens"
      completionTokens := usageNat usageJ "completionTokens"
      totalTokens := usageNat usageJ "totalTokens" }
  let file ← strField "auditEntry" "file" j
  let promptPreview ← strField "auditEntry" "promptPreview" j
  pure { runId, kind, providerId, model, stop, usage, file, promptPreview }

/-- Append one entry to the manifest (creating it if needed). Best-effort: a
single append syscall per run keeps interleaving unlikely, and the index is
rebuildable regardless. -/
public def appendIndex (dir : System.FilePath) (e : AuditEntry) : IO Unit := do
  IO.FS.createDirAll dir
  let line := Json.compress (encodeAuditEntry e) ++ "\n"
  let path := dir / indexFileName
  let handle ← IO.FS.Handle.mk path IO.FS.Mode.append
  handle.putStr line
  handle.flush

/-- Read and decode the manifest, skipping malformed lines (fail-soft on read;
the transcripts remain authoritative). Returns `[]` if there is no manifest. -/
public def readIndex (dir : System.FilePath) : IO (Array AuditEntry) := do
  let path := dir / indexFileName
  if !(← path.pathExists) then
    return #[]
  let raw ← IO.FS.readFile path
  let entries := (raw.splitOn "\n").filterMap fun line =>
    if !nonemptyText line then none
    else match parseJson line with
      | .error _ => none
      | .ok j => match decodeAuditEntry j with
        | .ok e => some e
        | .error _ => none
  return entries.toArray

/-- Rebuild the manifest by scanning every `<runId>.jsonl` transcript in `dir`
(excluding the manifest and any `.tmp`), decoding it, and rewriting the index
atomically. The index is a pure projection of the transcripts. -/
public def rebuildIndexWith {Tool : Type} (ts : ToolSet Tool) (dir : System.FilePath) :
    IO (Array AuditEntry) := do
  if !(← dir.pathExists) then
    return #[]
  let mut entries : Array AuditEntry := #[]
  for entry in ← dir.readDir do
    let name := entry.fileName
    if name == indexFileName || !name.endsWith ".jsonl" then
      continue
    let raw ← IO.FS.readFile entry.path
    match decodeJsonlWith ts raw with
    | .ok t => entries := entries.push (AuditEntry.ofTranscriptWith name t)
    | .error _ => pure ()   -- skip anything that is not a well-formed transcript
  let body := joinSep "\n" (entries.toList.map (fun e => Json.compress (encodeAuditEntry e)))
  let contents := if entries.isEmpty then "" else body ++ "\n"
  writeFileAtomic (dir / indexFileName) contents
  return entries

public def rebuildIndex (dir : System.FilePath) : IO (Array AuditEntry) :=
  rebuildIndexWith kernelTools dir

/-- Write a transcript's audit file atomically and append its manifest row.
The single source of truth is the transcript; the index is a convenience that
`rebuildIndex` can always regenerate. Returns the transcript path on success. -/
public def writeAuditIndexedWith {Tool : Type} (ts : ToolSet Tool) (dir : System.FilePath)
    (t : Transcript Tool) : IO (Except String System.FilePath) := do
  match ← writeAuditWith ts dir t with
  | .error e => return .error e
  | .ok path =>
    appendIndex dir (AuditEntry.ofTranscriptWith (t.runId ++ ".jsonl") t)
    return .ok path

public def writeAuditIndexed (dir : System.FilePath) (t : Transcript DemoTool) :
    IO (Except String System.FilePath) :=
  writeAuditIndexedWith kernelTools dir t

/-! ## Query helpers over the manifest -/

public def AuditEntry.finished (e : AuditEntry) : Bool :=
  match e.stop with | .finished => true | _ => false

public def AuditEntry.refused (e : AuditEntry) : Bool :=
  match e.stop with | .refused _ => true | _ => false

public def byProvider (entries : Array AuditEntry) (providerId : String) : Array AuditEntry :=
  entries.filter (·.providerId == providerId)

public def byKind (entries : Array AuditEntry) (kind : RunKind) : Array AuditEntry :=
  entries.filter (·.kind == kind)

public def refusedRuns (entries : Array AuditEntry) : Array AuditEntry :=
  entries.filter AuditEntry.refused

/-- Total tokens across the indexed runs (missing counts treated as 0). -/
public def totalTokens (entries : Array AuditEntry) : Nat :=
  entries.foldl (init := 0) fun acc e => acc + (e.usage.totalTokens.getD 0)

#guard
  let e : AuditEntry := {
    runId := "run-1", kind := .ask, providerId := "ollama", model := "x"
    stop := .finished, usage := { totalTokens := some 20 }, file := "run-1.jsonl"
    promptPreview := "hi"
  }
  match decodeAuditEntry (encodeAuditEntry e) with
  | .ok e2 => e2 == e
  | .error _ => false

#guard
  let a : AuditEntry := {
    runId := "a", kind := .ask, providerId := "ollama", model := "x"
    stop := .finished, file := "a.jsonl"
  }
  let b : AuditEntry := {
    runId := "b", kind := .extract, providerId := "openai", model := "y"
    stop := .refused 3, usage := { totalTokens := some 5 }, file := "b.jsonl"
  }
  let es := #[a, b]
  (byProvider es "ollama").size == 1 &&
    (byKind es .extract).size == 1 &&
    (refusedRuns es).size == 1 &&
    totalTokens es == 5

end

end LeanAgent
