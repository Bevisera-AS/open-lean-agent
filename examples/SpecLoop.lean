import Lean.Data.Json
import LeanAgent.Agents
import LeanAgent.OpenAICompat
import LeanAgent.Roles
import LeanAgent.Workbench

/-!
# The spec loop: builder, referee, reviewer

lean-spec's bench (`lean-spec/bench`) runs one loop. A **builder** agent writes
`Spec.lean` (requirements with examples) and the program in a workspace. A
**referee**, which is a program and not an agent, gates every step: `lake exe spec
check` must pass, `./test.sh` runs the examples, and `./next` releases the next
change request only when the tests pass. A **reviewer** audits the finished
workspace into typed findings. This example is that loop on lean-agent's pieces:

* the builder is an `Agent` over the closed `Workbench` tool type (read, write,
  list, run a workspace script, pipe an input through the program, run the spec
  CLI) from `LeanAgent.Workbench`, run by the kernel's one loop, `askWith`, which
  runs every tool call of a turn in order (GLM returns parallel calls even with
  `parallel_tool_calls` off);
* the referee is `Referee`: the workspace scripts and `stage.json`, which `./next`
  writes; `refereeGate` is the loop's finish hook (`AskPolicy.onFinish`) and reads
  it after every model finish to accept the finish or nudge the builder in the same
  history, as the Python driver did;
* the reviewer is lean-agent's read-only `Roles.Reader` agent, whose findings come
  back through the fail-closed `OutputContract` as `Finding` values mirroring
  `lean-spec/bench/Findings.lean`, so a malformed finding is refused, not logged.

No lean-spec import: the referee is a subprocess and `Finding` is local.

Run offline (scripted completers, the stub referee in `fixtures/spec-loop`):

```sh
lake exe spec-loop
```

Run live against a bench workspace, GLM through z.ai (`GLM_API_KEY`):

```sh
lake exe spec-loop live ../lean-spec/bench lru py lean 11 glm-4.7-flash [--review]
```

The live run prepares the workspace with `bench/subagent.py prep`, writes the
audited transcript and `meta.json` into the run directory, and scores with
`bench/check.py`, so its line in `results.jsonl` is comparable with the
Python-driven runs.
-/

open Lean
open LeanAgent

namespace SpecLoop

/-- The same completer, counting the completions it returns (`meta.json` wants the
number of model calls). -/
def counting (c : Completer) : IO (Completer × IO Nat) := do
  let n ← IO.mkRef 0
  let counted : Completer := {
    post := fun url body => do
      let r ← c.post url body
      if let .ok _ _ := r then n.modify (· + 1)
      pure r
  }
  pure (counted, n.get)

/-! ## The reviewer's findings, as a fail-closed contract -/

/-- Mirrors `LeanSpec.FindingKind` without importing it. -/
inductive FindingKind where
  | specDrift | reprDrift | bug | testGap | flaw
  deriving Repr, BEq

def FindingKind.text : FindingKind → String
  | .specDrift => "specDrift"
  | .reprDrift => "reprDrift"
  | .bug => "bug"
  | .testGap => "testGap"
  | .flaw => "flaw"

def FindingKind.parse : String → Option FindingKind
  | "specDrift" => some .specDrift
  | "reprDrift" => some .reprDrift
  | "bug" => some .bug
  | "testGap" => some .testGap
  | "flaw" => some .flaw
  | _ => none

/-- One defect in one run: the row shape of `lean-spec/bench/Findings.lean`. -/
structure Finding where
  run : String
  req : String
  kind : FindingKind
  severity : Nat
  evidence : String
  note : String
  deriving Repr, BEq

def Finding.wellFormed (f : Finding) : Bool :=
  nonemptyText f.run && nonemptyText f.req && nonemptyText f.evidence && nonemptyText f.note &&
    1 ≤ f.severity && f.severity ≤ 3

/-- The finding as a `bench/Findings.lean` row. -/
def Finding.render (f : Finding) : String :=
  s!"⟨{Json.str f.run}, {Json.str f.req}, .{f.kind.text}, {f.severity}, {Json.str f.evidence}, {Json.str f.note}⟩"

def encodeFinding (f : Finding) : Json :=
  Json.mkObj [
    ("run", Json.str f.run), ("req", Json.str f.req), ("kind", Json.str f.kind.text),
    ("severity", (f.severity : Json)), ("evidence", Json.str f.evidence), ("note", Json.str f.note)
  ]

/-- The row's fields, once: the item schema and the decoder's unknown-field
check both come from this list. -/
def findingFields : List (String × Json) := [
  ("run", Json.mkObj [("type", Json.str "string")]),
  ("req", Json.mkObj [("type", Json.str "string")]),
  ("kind", Json.mkObj [("type", Json.str "string"),
    ("enum", Json.arr (#["specDrift", "reprDrift", "bug", "testGap", "flaw"].map Json.str))]),
  ("severity", Json.mkObj [("type", Json.str "integer")]),
  ("evidence", Json.mkObj [("type", Json.str "string")]),
  ("note", Json.mkObj [("type", Json.str "string")])
]

def findingSchema : Json := objectParams (findingFields.map (·.1)).toArray findingFields

def decodeFinding (j : Json) : Except DecodeError Finding := do
  let ctx := "finding"
  let o ← asObj ctx j
  exactFields ctx (findingFields.map (·.1)) o
  let run ← strField ctx "run" j
  let req ← strField ctx "req" j
  let kindText ← strField ctx "kind" j
  let some kind := FindingKind.parse kindText
    | .error (.invalidTag ctx "kind" kindText)
  let severity ← natField ctx "severity" j
  let evidence ← strField ctx "evidence" j
  let note ← strField ctx "note" j
  pure { run, req, kind, severity, evidence, note }

def encodeFindings (fs : Array Finding) : Json :=
  Json.mkObj [("findings", Json.arr (fs.map encodeFinding))]

def decodeFindings (j : Json) : Except DecodeError (Array Finding) := do
  (← arrField "findings" "findings" j).mapM decodeFinding

def findingsContract : OutputContract (Array Finding) :=
  OutputContract.ofFields "findings"
    [("findings", Json.mkObj [("type", Json.str "array"), ("items", findingSchema)])]
    decodeFindings encodeFindings (fun fs => fs.all Finding.wellFormed)

#guard findingsContract.schemaAgrees ["findings"]
#guard closedObjectFields findingSchema == some ["run", "req", "kind", "severity", "evidence", "note"]

private def sampleFinding : Finding := {
  run := "lru-py-lean-haiku-s11", req := "R1", kind := .specDrift, severity := 2
  evidence := "Spec.lean:12", note := "invented an error case" }

#guard findingsContract.roundTrips [#[sampleFinding], #[]]

-- Severity 0 and an unknown kind fail closed.
#guard
  match findingsContract.accept (encodeFindings #[{ sampleFinding with severity := 0 }]) with
  | .error (.illFormed "findings" _) => true
  | _ => false
#guard
  match decodeFinding (Json.mkObj [("run", Json.str "r"), ("req", Json.str "-"), ("kind", Json.str "typo"),
      ("severity", (2 : Json)), ("evidence", Json.str "x"), ("note", Json.str "y")]) with
  | .error (.invalidTag "finding" "kind" "typo") => true
  | _ => false

/-! ## The reviewer -/

def reviewerSystem : String :=
  "You are the reviewer. Audit a finished workspace against the ground-truth requirements: " ++
    "read Spec.lean and the program with the tools, compare the spec with the task and the " ++
    "program with the spec, and name every defect with its location. Invented behaviour the " ++
    "task never defines is spec drift, not a bug; a correct program with a fragile test is a flaw. " ++
    "Do not fix anything."

def reviewerAgent (cfg : ProviderConfig) (ws : System.FilePath) : Agent Roles.Reader := {
  name := "reviewer"
  system := reviewerSystem
  cfg
  tools := Roles.readerTools
  runner := Roles.readerRunner ws
  policy := { maxTurns := 12 }
}

def findingsPrompt (runId audit : String) : String :=
  s!"Run id: {runId}. From this audit, return a findings JSON object: one finding per defect " ++
    s!"with run, req (the ground-truth requirement id or \"-\"), kind (specDrift, reprDrift, bug, " ++
    s!"testGap or flaw), severity 1 to 3, evidence (file:line or a case id) and a one-sentence note.\n\n{audit}"

/-- Audit a workspace: the reader agent looks, then the contract extracts typed findings. -/
def review (cfg : ProviderConfig) (ws : System.FilePath) (reviewC extractC : Completer)
    (runId prompt : String) : IO (Except ExtractError (Array Finding)) := do
  let t ← (reviewerAgent cfg ws).run reviewC prompt s!"{runId}-review"
  let audit := (Agent.finalText t).getD "(the reviewer did not finish)"
  extractTyped findingsContract extractC cfg (findingsPrompt runId audit)

/-! ## Scripted completers and the hermetic run -/

/-- Return the replies in order; error once the script is exhausted. -/
def scripted (replies : List String) : IO Completer := do
  let box ← IO.mkRef replies
  pure {
    post := fun _url _body => do
      match ← box.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest => box.set rest; pure (.ok 200 r)
  }

def call (id name : String) (args : List (String × Json)) : String :=
  wrapToolCall id name (Json.compress (Json.mkObj args))

def write (id path content : String) : String :=
  call id "write_file" [("path", Json.str path), ("content", Json.str content)]

/-- One reply carrying several tool calls, as GLM sends them. -/
def calls (items : List (String × String × List (String × Json))) : String :=
  wrapToolCalls (items.toArray.map fun (id, name, args) => (id, name, Json.compress (Json.mkObj args)))

/-- The first two lines of a tool result: the exit code and what the script said. -/
def headLines (s : String) : String :=
  joinSep " | " (((s.splitOn "\n").filter nonemptyText).take 2 |>.map fun l => (l.take 100).copy)

def describe (e : Event Workbench) : String :=
  match e with
  | .invoke _ tool =>
    s!"  → {workbenchTools.name tool} {(Json.compress (workbenchTools.argumentsJson tool)).take 70}"
  | .result _ output => s!"  ← {headLines output}"
  | .repair turn detail => s!"  ! turn {turn}: {detail}"
  | .reasoning _ _ => "  (reasoning)"
  | .finish content => s!"  ■ {content}"

def specV1 : String := r#"import LeanSpec
open LeanSpec.Core Lean

/-- get of an absent key is null -/
@[requirement must] def R1 : IOSig → Prop := Req.holds [
  ex "miss" (json% {"ops":[["get","a"]]}) (json% {"results":[null]})]
"#

def specV2 : String := specV1 ++ r#"
/-- put stores a value that get returns -/
@[requirement must] def R2 : IOSig → Prop := Req.holds [
  ex "put-get" (json% {"ops":[["put","a",1],["get","a"]]}) (json% {"results":[null,1]})]
"#

def progV1 : String := r#"cat > /dev/null
echo '{"results":[null]}'
"#

def progV2 : String := r#"in=$(cat)
case "$in" in
  *'"put"'*) echo '{"results":[null,1]}' ;;
  *) echo '{"results":[null]}' ;;
esac
"#

def hermeticBrief : String :=
  "Work in the current directory. Deliver Spec.lean, the requirements with examples in lean-spec " ++
    "(run `spec help` first; `spec check` must pass), and the program prog.sh, which reads one JSON " ++
    "value on stdin and writes one on stdout. The examples are the tests: ./test.sh runs them. " ++
    "When ./test.sh passes, run ./next for the next change request, apply it, and repeat until " ++
    "there are no more. Then reply DONE.\n\nTASK\nBuild a cache simulator: input " ++
    "{\"ops\":[op,...]}, op is [\"get\", key]; get returns null when absent. " ++
    "Output {\"results\":[...]}, one entry per op."

/-- The builder's moves, as the model would make them: manual, spec, program,
check and test in one reply, next; an early finish that the gate turns into a nudge; the change
request applied to the spec first, so the tests fail and `./next` refuses; then
the program, and `./next` releases the end. -/
def builderScript : List String := [
  call "b1" "spec" [("command", Json.str "help")],
  write "b2" "Spec.lean" specV1,
  write "b3" "prog.sh" progV1,
  calls [("b4", "spec", [("command", Json.str "check")]), ("b5", "run_script", [("name", Json.str "test")])],
  call "b6" "run_script" [("name", Json.str "next")],
  wrapContent "Applied the change request.",
  write "b7" "Spec.lean" specV2,
  call "b8" "run_script" [("name", Json.str "test")],
  call "b9" "run_script" [("name", Json.str "next")],
  write "b10" "prog.sh" progV2,
  call "b11" "run_script" [("name", Json.str "next")],
  wrapContent "DONE"
]

def fixtureFiles : List String := ["build", "run", "test.sh", "next", "spec"]

/-- A fresh copy of the fixture under the sandbox, scripts executable. -/
def prepareHermetic (sandbox : System.FilePath) : IO System.FilePath := do
  if ← sandbox.pathExists then IO.FS.removeDirAll sandbox
  let ws := sandbox / "ws"
  IO.FS.createDirAll ws
  for name in fixtureFiles do
    IO.FS.writeFile (ws / name) (← IO.FS.readFile ("fixtures" / "spec-loop" / name))
    let _ ← IO.Process.run { cmd := "chmod", args := #["+x", (ws / name).toString] }
  pure ws

def hermetic : IO UInt32 := do
  let ws ← prepareHermetic (".lean-agent-sandbox" / "spec-loop")
  let referee : Referee := { ws, specCmd := #["./spec"], timeoutSecs := 30 }
  let cfg := ollama
  let runId := "spec-loop-demo"

  -- 1) The builder, gated by the referee.
  let (c, modelCalls) ← counting (← scripted builderScript)
  let t ← (builderAgent cfg referee { stages := 2 }).run c hermeticBrief runId
  let calls ← modelCalls
  IO.eprintln s!"[builder] {calls} model calls, stop={repr t.stop}"
  for e in t.events do IO.eprintln (describe e)
  let passed ← referee.stagesPassed
  IO.eprintln s!"[referee] stages released: {passed}/2"
  match ← writeAuditWith workbenchTools (ws.parent.getD ws) t with
  | .ok path => IO.eprintln s!"[audit] {path}"
  | .error e => IO.eprintln s!"[audit] not written: {e}"; return 1

  -- 2) The reviewer: reads, then the contract extracts findings. The first
  --    extract reply has severity 0 and is refused; the repaired one is accepted.
  let reviewC ← scripted [
    call "r1" "read_file" [("path", Json.str "prog.sh")],
    wrapContent ("prog.sh answers by whether the input mentions \"put\", not by key: " ++
      "[\"put\",\"b\",1] then [\"get\",\"a\"] returns 1. Spec.lean matches the task.")
  ]
  let bug : Finding := {
    run := runId, req := "R2", kind := .bug, severity := 3, evidence := "prog.sh:3"
    note := "answers by the presence of \"put\" in the input, not by key" }
  let extractC ← scripted [
    wrapContent (Json.compress (encodeFindings #[{ bug with severity := 0 }])),
    wrapContent (Json.compress (encodeFindings #[bug]))
  ]
  let findings ← match ← review cfg ws reviewC extractC runId
      "Audit the workspace against the task: get returns null when absent; put stores a value that get returns." with
    | .ok fs => pure fs
    | .error e => IO.eprintln s!"[reviewer] refused: {e.pretty}"; return 1
  IO.eprintln s!"[reviewer] {findings.size} finding(s), as bench/Findings.lean rows:"
  for f in findings do IO.println f.render

  if t.stop != .finished || passed != 2 || findings != #[bug] then
    IO.eprintln "[spec-loop] unexpected outcome"
    return 1
  return 0

/-! ## The live run: one bench seed, scored by the bench -/

/-- GLM through z.ai, as the Python driver used it. -/
def zai (model : String) : ProviderConfig := {
  provider := .glm
  config := .glm {
    baseUrl := "https://api.z.ai/api/paas/v4", model, apiKeyEnv := "GLM_API_KEY", maxTokens := some 32768 }
}

def python (args : Array String) : IO String := do
  let out ← IO.Process.output { cmd := "python3", args }
  if out.exitCode != 0 then
    throw (IO.userError s!"python3 {args[0]?.getD ""} failed (exit {out.exitCode}):\n{out.stderr}")
  pure out.stdout

/-- `glm-4.7-flash` becomes `glm47flash`, as in the Python driver, plus `la` for this driver. -/
def modelLabel (model : String) : String :=
  String.ofList (model.toList.filter (fun c => c != '.' && c != '-')) ++ "la"

def stageNames : List String := ["base", "cr1", "cr2"]

/-- `meta.json` as `bench/check.py` reads it: the stages released, the exact
usage and the driver. -/
def updateMeta (rdir : System.FilePath) (passed calls : Nat) (wallS : Nat) (usage : Usage) :
    IO Unit := do
  let path := rdir / "meta.json"
  let m ← match Json.parse (← IO.FS.readFile path) with
    | .ok j => pure j
    | .error e => throw (IO.userError s!"meta.json: {e}")
  let stages := (stageNames.take passed).toArray.mapIdx fun i n => Json.mkObj [
    ("stage", Json.str n), ("is_error", Json.bool false), ("turns", ((if i == 0 then calls else 0) : Json)),
    ("usage", Json.mkObj []), ("wall_s", ((if i == 0 then wallS else 0) : Json))]
  let exact := Json.mkObj [
    ("input_tokens", (usage.promptTokens.getD 0 : Json)), ("cache_read_input_tokens", (0 : Json)),
    ("cache_creation_input_tokens", (0 : Json)), ("output_tokens", (usage.completionTokens.getD 0 : Json)),
    ("api_calls", (calls : Json))]
  let m := m.setObjVal! "stages" (Json.arr stages)
    |>.setObjVal! "usage_exact" exact
    |>.setObjVal! "driver" (Json.str "lean-agent")
  IO.FS.writeFile path (m.pretty ++ "\n")

def live (args : List String) : IO UInt32 := do
  let bench :: task :: lang :: arm :: seed :: model :: rest := args
    | IO.eprintln "usage: spec-loop live BENCH TASK LANG ARM SEED MODEL [--review]"; return 2
  let bench ← IO.FS.realPath bench
  let some runs := bench.parent.bind (·.parent) |>.map (· / "lean-spec-core-runs")
    | IO.eprintln "bench directory has no grandparent"; return 2
  let cfg := zai model
  -- Probe the key before a workspace exists: a run that cannot reach the model is
  -- not a run, and must not be prepared, scored or appended to results.
  if let some keyEnv := cfg.apiKeyEnv then
    if (← IO.getEnv keyEnv).isNone then
      IO.eprintln s!"[live] {keyEnv} is not set; export it in this shell first"
      return 2
  let label := modelLabel model
  let runId : String :=
    (← python #[(bench / "subagent.py").toString, "prep", task, lang, arm, seed, label]).trimAscii.copy
  let rdir := runs / runId
  let ws := rdir / "ws"
  let brief ← IO.FS.readFile (ws / "BRIEF.txt")
  let referee : Referee := { ws }
  IO.eprintln s!"[live] {runId} in {rdir}"
  let t0 ← IO.monoMsNow
  let (c, modelCalls) ← counting (curlCompleter cfg)
  let t ← (builderAgent cfg referee).run c brief runId
  let calls ← modelCalls
  let wallS := ((← IO.monoMsNow) - t0) / 1000
  let passed ← referee.stagesPassed
  IO.eprintln s!"[builder] stop={repr t.stop} calls={calls} stages={passed}/3 wall={wallS}s"
  match ← writeAuditWith workbenchTools rdir t with
  | .ok path => IO.eprintln s!"[audit] {path}"
  | .error e => IO.eprintln s!"[audit] not written: {e}"
  if calls == 0 then
    IO.eprintln "[live] the model was never reached; not scored (see the audit's repair event)"
    IO.FS.removeDirAll rdir
    return 1
  updateMeta rdir passed calls wallS t.usage
  let scored ← python #[(bench / "check.py").toString, rdir.toString]
  match Json.parse scored with
  | .ok r =>
    let hidden := (r.getObjVal? "hidden").toOption.bind fun h =>
      (h.getObjValAs? Nat "passed").toOption.bind fun p => (h.getObjValAs? Nat "total").toOption.map (p, ·)
    let specOk := (r.getObjVal? "spec_drift").toOption.bind fun s => (s.getObjValAs? Bool "ok").toOption
    IO.println (Json.compress (Json.mkObj [
      ("run", Json.str runId), ("stages", (passed : Json)),
      ("hidden", match hidden with | some (p, n) => Json.str s!"{p}/{n}" | none => Json.null),
      ("spec_ok", match specOk with | some b => Json.bool b | none => Json.null),
      ("out", (t.usage.completionTokens.getD 0 : Json)), ("calls", (calls : Json))]))
  | .error e => IO.eprintln s!"[score] unreadable: {e}\n{scored}"
  if rest.contains "--review" then
    let taskJson ← IO.FS.readFile (bench / "tasks" / task / "task.json")
    let report ← referee.spec "report"
    let prompt := s!"Ground truth (task.json):\n{taskJson}\n\n`lake exe spec report ./run`:\n{report}\n\n" ++
      "List the workspace, read Spec.lean and the program, then report every defect."
    match ← review cfg ws (curlCompleter cfg) (curlCompleter cfg) runId prompt with
    | .ok fs =>
      IO.FS.writeFile (rdir / "findings.json") ((encodeFindings fs).pretty ++ "\n")
      IO.eprintln s!"[reviewer] {fs.size} finding(s) in {rdir / "findings.json"}"
      for f in fs do IO.println f.render
    | .error e => IO.eprintln s!"[reviewer] refused: {e.pretty}"
  return 0

end SpecLoop

def main (args : List String) : IO UInt32 :=
  match args with
  | [] => SpecLoop.hermetic
  | "live" :: rest => SpecLoop.live rest
  | _ => do IO.eprintln "usage: spec-loop | spec-loop live BENCH TASK LANG ARM SEED MODEL [--review]"; return 2
