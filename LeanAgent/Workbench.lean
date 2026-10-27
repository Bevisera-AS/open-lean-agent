module

public import Lean.Data.Json
public import LeanAgent.Agents
public import LeanAgent.Files
public import LeanAgent.Json
public import LeanAgent.Samples
public import LeanAgent.ToolDSL
public import LeanAgent.Verify
public meta import Lean.Data.Json
public meta import LeanAgent.Json
public meta import LeanAgent.Samples
public meta import LeanAgent.ToolDSL

/-!
The spec loop's builder catalog and referee. No LeanSpec import: a bridge package
imports this module and supplies the finding contract. `examples/SpecLoop.lean`
keeps the hermetic script and its local `Finding`.
-/

namespace LeanAgent

open Lean

public section

/-! ## The builder's closed catalog -/

/-- What the builder may do. Every constructor is one workspace effect; there is
no shell, so a command outside this list cannot be invoked. -/
public inductive Workbench where
  | readFile (path : String)
  | writeFile (path content : String)
  | listDir (path : String)
  /-- `build`, `test` or `next`: the workspace scripts. -/
  | runScript (name : String)
  /-- Pipe an input through `./run`. -/
  | runProg (input : String)
  /-- `lake exe spec <command>`. -/
  | spec (command : String)
  deriving Repr, BEq

public def workbenchTools : ToolSet Workbench := mkToolSet [
  toolDecl1 "read_file" "Read a UTF-8 text file in the workspace by relative path."
    "path" Workbench.readFile (fun | .readFile p => some p | _ => none),
  toolDecl2 "write_file"
    "Create or overwrite a workspace file by relative path; parent directories are created."
    "path" "content" Workbench.writeFile (fun | .writeFile p c => some (p, c) | _ => none),
  toolDecl1 "list_dir" "List a workspace directory; `.` is the workspace."
    "path" Workbench.listDir (fun | .listDir p => some p | _ => none),
  { toolDecl1 "run_script"
      ("Run a workspace script: `build` (./build), `test` (./test.sh), or `next` (./next: " ++
        "prints the next change request when the tests pass). Returns the exit code and output.")
      "name" Workbench.runScript (fun | .runScript n => some n | _ => none) with effect := .verify },
  { toolDecl1 "run_prog" "Pipe `input` into ./run, the program, and return its exit code and output."
      "input" Workbench.runProg (fun | .runProg i => some i | _ => none) with effect := .verify },
  { toolDecl1 "spec"
      ("Run `lake exe spec <command>`: `help` (the manual, read it first), `check`, `emit`, " ++
        "`statement`, `test` (the examples against ./run) or `report`.")
      "command" Workbench.spec (fun | .spec c => some c | _ => none) with effect := .verify }
]

#guard (workbenchTools.specs.map (·.name)).toList ==
  ["read_file", "write_file", "list_dir", "run_script", "run_prog", "spec"]
#guard workbenchTools.covers (samples% Workbench)

-- Refusal is structural: there is no shell in the catalog.
#guard
  match workbenchTools.decode "run_command" (Json.mkObj [("command", Json.str "rm -rf /")]) with
  | .error (.invalidTag "tool" "name" "run_command") => true
  | _ => false

/-! ## The referee: the workspace scripts and the stage gate -/

/-- The programs that judge the builder. `specCmd` is `lake exe spec` in a bench
workspace and `./spec` in the hermetic fixture. Commands run in the workspace,
bounded by `timeoutSecs`, with the API key withheld from their environment. -/
public structure Referee where
  ws : System.FilePath
  specCmd : Array String := #["lake", "exe", "spec"]
  timeoutSecs : Nat := 300
  withhold : Array String := #["GLM_API_KEY"]

/-- Output returned to the model is clipped, as the Python driver clipped it. -/
def maxOutput : Nat := 12000

def clipOutput (s : String) : String :=
  if s.length ≤ maxOutput then s else (s.take maxOutput).copy ++ "\n...[truncated]"

/-- Run one command in the workspace; the result is always a string the model
can read, never an exception. -/
public def Referee.run (r : Referee) (cmd : String) (args : Array String) : IO String := do
  try
    let spawn : IO.Process.SpawnArgs :=
      { cmd, args, cwd := some r.ws, env := r.withhold.map (fun k => (k, none)) }
    let (out, timedOut) ← Verify.runBounded spawn r.timeoutSecs
    if timedOut then return s!"ERROR: command timed out after {r.timeoutSecs}s"
    let text := out.stdout ++ (if out.stderr.isEmpty then "" else "\n[stderr]\n" ++ out.stderr)
    pure s!"[exit {out.exitCode}]\n{clipOutput text}"
  catch e => pure s!"ERROR: {e}"

public def Referee.script (r : Referee) (name : String) : IO String :=
  match name with
  | "build" => r.run "./build" #[]
  | "test" => r.run "./test.sh" #[]
  | "next" => r.run "./next" #[]
  | other => pure s!"ERROR: unknown script `{other}`; use build, test or next"

public def Referee.prog (r : Referee) (input : String) : IO String :=
  r.run "sh" #["-c", "printf %s \"$1\" | ./run", "sh", input]

/-- The spec CLI, one subcommand at a time; `test` and `report` take `./run`. -/
public def Referee.spec (r : Referee) (command : String) : IO String :=
  match (command.splitOn " ").filter (· != "") with
  | [sub] =>
    if ["help", "check", "emit", "statement"].contains sub then
      r.run r.specCmd[0]! (r.specCmd.extract 1 r.specCmd.size ++ #[sub])
    else if ["test", "report"].contains sub then
      r.run r.specCmd[0]! (r.specCmd.extract 1 r.specCmd.size ++ #[sub, "./run"])
    else pure s!"ERROR: unknown spec command `{sub}`"
  | _ => pure "ERROR: spec takes one command: help, check, emit, statement, test or report"

/-- `./next` records the stages passed so far in `stage.json` beside the workspace. -/
public def Referee.stagesPassed (r : Referee) : IO Nat := do
  let path := (r.ws.parent.getD r.ws) / "stage.json"
  unless ← path.pathExists do return 0
  match Json.parse (← IO.FS.readFile path) with
  | .ok j => pure ((j.getObjValAs? Nat "i").toOption.getD 0)
  | .error _ => pure 0

public def workbenchRunner (r : Referee) : ToolRunner Workbench := {
  run := fun
    | .readFile p => Files.readFileIn r.ws p
    | .writeFile p c => Files.writeFileIn r.ws p c
    | .listDir p => Files.listDirIn r.ws p
    | .runScript n => r.script n
    | .runProg i => r.prog i
    | .spec c => r.spec c
}

/-! ## The builder: an agent whose finish gate is the referee -/

/-- Hermetic system text. The production bridge replaces this with the
`roleBuilder` skill; this string is what `lake exe spec-loop` sends. -/
public def builderSystem : String :=
  "You are a coding agent. Use the tools to read and write files in your workspace and to run " ++
    "its scripts: run_script build is ./build, run_script test is ./test.sh, run_script next is " ++
    "./next, run_prog pipes an input into ./run, and spec runs `lake exe spec <command>`. " ++
    "Be economical: no explanations."

/-- The bounds the Python driver used. `stages` is how many `./next` releases
make a run complete (three in the bench: base, cr1, cr2). -/
public structure LoopPolicy where
  maxTurns : Nat := 120
  maxNudges : Nat := 3
  stages : Nat := 3

def nudge : String :=
  "Not finished: make ./test.sh pass, then run ./next and apply each change request until " ++
    "./next says there are no more."

/-- The referee's gate as the kernel's finish hook. A finish is accepted once
`./next` has released every stage, or once `maxNudges` nudges are spent; otherwise
it is a nudge, kept in the same history. Retry, truncation, reasoning and the
transcript stay the kernel's. -/
public def refereeGate (r : Referee) (p : LoopPolicy) (info : FinishInfo Workbench) :
    IO FinishVerdict := do
  let passed ← r.stagesPassed
  if passed ≥ p.stages || info.nudges ≥ p.maxNudges then pure .accept
  else pure (.nudge s!"finished with {passed}/{p.stages} stages released; nudged" nudge)

public def builderAgent (cfg : ProviderConfig) (r : Referee) (p : LoopPolicy := {}) : Agent Workbench := {
  name := "builder"
  system := builderSystem
  cfg
  tools := workbenchTools
  runner := workbenchRunner r
  policy := { maxTurns := p.maxTurns, onFinish := some (refereeGate r p) }
}

end

end LeanAgent
