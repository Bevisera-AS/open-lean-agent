import Lean.Data.Json
import LeanAgent.Curl
import LeanAgent.Step
import LeanAgent.Live
import LeanAgent.Transcript
import LeanAgent.Arxiv
import LeanAgent.OpenAICompat
import LeanAgent.OutputContract
import LeanAgent.Extract
import LeanAgent.Tools
import LeanAgent.Ask
import LeanAgent.Generation
import LeanAgent.AuditIndex
import LeanAgent.Roles
import LeanAgent.Concurrent
import LeanAgent.Verify
import LeanAgent.Build

open LeanAgent

def assertTrue (label : String) (condition : Bool) : IO Unit := do
  if !condition then
    throw <| IO.userError s!"test failed: {label}"

def importModule? (line : String) : Option String :=
  let t := line.trimAscii.copy
  let rest :=
    if t.startsWith "public meta import " then (t.dropPrefix "public meta import ").copy
    else if t.startsWith "public import " then (t.dropPrefix "public import ").copy
    else if t.startsWith "import " then (t.dropPrefix "import ").copy
    else ""
  if rest.isEmpty then none
  else some (String.ofList (rest.toList.takeWhile (fun c => !c.isWhitespace)))

def forbiddenInAgent (mod : String) : Bool :=
  mod == "LeanSpec" || mod.startsWith "LeanSpec." ||
    mod == "LeanSpecAgent" || mod.startsWith "LeanSpecAgent."

def assertNoForbidden (label : String) (path : System.FilePath) : IO Unit := do
  let raw ← IO.FS.readFile path
  for line in raw.splitOn "\n" do
    match importModule? line with
    | some m =>
      if forbiddenInAgent m then
        throw <| IO.userError s!"test failed: {label} {path} imports {m}"
    | none => pure ()

def checkImportFirewall : IO Unit := do
  let files := (← (⟨"LeanAgent"⟩ : System.FilePath).walkDir).filter fun p =>
    p.toString.endsWith ".lean"
  for path in files do
    assertNoForbidden "LeanAgent" path
  assertNoForbidden "LeanAgentQuery" ⟨"LeanAgentQuery.lean"⟩
  assertNoForbidden "LeanAgentTests" ⟨"LeanAgentTests.lean"⟩

/-- Builder role: the toolchain, `lake build`, `lake test` and the kernel
re-checker, run against the two fixture packages under `fixtures/`. -/
def builderTests : IO Unit := do
  -- Diagnostics parse in both the `lake` and the plain `lean` spelling.
  let lakeStyle := Build.parseDiagnostics "✖ [2/3] Building Bad\nerror: Bad.lean:4:15: Type mismatch\nerror: build failed"
  assertTrue "lake-style diagnostic parses with file, line, column"
    (lakeStyle.map (fun d => (d.file, d.line, d.column, d.severity)) == #[("Bad.lean", 4, 15, "error")] &&
      lakeStyle[0]?.map (·.message) == some "Type mismatch")
  let leanStyle := Build.parseDiagnostics "A/B.lean:10:2: warning: unused variable `x`"
  assertTrue "lean-style diagnostic parses"
    (leanStyle.map (fun d => (d.file, d.line, d.severity)) == #[("A/B.lean", 10, "warning")])
  assertTrue "a build summary line is not a diagnostic"
    ((Build.parseDiagnostics "error: build failed").isEmpty)
  -- Targets and module names cannot smuggle flags or shell words.
  assertTrue "module and target names are checked"
    (Build.safeName "BuildOk.Basic" && Build.safeName "build-ok-tests" && Build.safeName "«build-ok»" &&
      !Build.safeName "--help" && !Build.safeName "a b" && !Build.safeName "" && !Build.safeName "x;rm")
  -- Closed catalog, every tool marked as a verification.
  assertTrue "builder decodes lake_build"
    (match Roles.decodeBuilder "lake_build" (Lean.Json.mkObj
        [("project", Lean.Json.str "build-ok"), ("target", Lean.Json.str "default")]) with
     | .ok (.lakeBuild "build-ok" "default") => true
     | _ => false)
  assertTrue "builder refuses file writes"
    (match Roles.decodeBuilder "write_file" (Lean.Json.mkObj
        [("path", Lean.Json.str "x"), ("content", Lean.Json.str "y")]) with
     | .error (.invalidTag "tool" "name" "write_file") => true
     | _ => false)
  assertTrue "builder catalog is exactly the five tools"
    ((Roles.builderSpecs.map (·.name)).toList ==
      ["toolchain", "lake_build", "lake_test", "leanchecker", "leanchecker_paranoid"])
  assertTrue "every builder tool is a verification, none commits"
    ([Roles.Builder.toolchain "p", .lakeBuild "p" "t", .lakeTest "p", .leanchecker "p" "M",
        .leancheckerParanoid "p" "M"].all (Roles.builderTools.effect · == .verify))
  -- Runs stay inside the sandbox root.
  let sandbox : Build.Sandbox := { root := (← IO.currentDir) / "fixtures", timeoutSecs := 600 }
  let escaped ← Build.lakeBuild sandbox "../.." "default"
  assertTrue "a project outside the sandbox is refused" (!escaped.ok && escaped.diagnostics.isEmpty &&
    (escaped.output.splitOn "outside").length > 1)
  let flagged ← Build.lakeBuild sandbox "build-ok" "--help"
  assertTrue "a flag as target is refused" (!flagged.ok)
  -- The real thing.
  let version ← Build.toolchain sandbox "build-ok"
  assertTrue "toolchain reports the pinned Lean" ((version.splitOn "v4.35.0").length > 1)
  let good ← Build.lakeBuild sandbox "build-ok" "default"
  assertTrue "lake_build passes on the good fixture" (good.ok && good.diagnostics.isEmpty)
  let bad ← Build.lakeBuild sandbox "build-fail" "default"
  assertTrue "lake_build fails on the bad fixture and points at Bad.lean line 4"
    (!bad.ok && bad.diagnostics.any (fun d => d.file == "Bad.lean" && d.line == 4 && d.severity == "error"))
  let tested ← Build.lakeTest sandbox "build-ok"
  assertTrue "lake_test runs the fixture's test driver" tested.ok
  let kernel ← Build.kernelCheck sandbox "build-ok" "BuildOk.Basic" false
  assertTrue "leanchecker re-checks a built module" kernel.ok
  let paranoid ← Build.kernelCheck sandbox "build-ok" "BuildOk.Basic" true
  assertTrue "leanchecker-paranoid re-checks a built module" paranoid.ok
  let missing ← Build.kernelCheck sandbox "build-ok" "BuildOk.Nope" false
  assertTrue "leanchecker fails on a module that does not exist" (!missing.ok)
  assertTrue "a verdict renders OK or FAIL with its diagnostics"
    (good.render.startsWith "OK" && bad.render.startsWith "FAIL" && (bad.render.splitOn "Bad.lean:4").length > 1)

/-- Sandbox paths: the lexical rule plus symlink confinement, and the process
bound that needs no `timeout` binary. -/
def sandboxTests : IO Unit := do
  IO.FS.withTempDir fun dir => do
    let root := dir / "root"
    let outside := dir / "outside"
    IO.FS.createDirAll root
    IO.FS.createDirAll outside
    IO.FS.writeFile (outside / "secret.txt") "secret"
    IO.FS.writeFile (root / "inner.txt") "inner"
    let ln (target link : System.FilePath) : IO Unit := do
      let out ← IO.Process.output { cmd := "ln", args := #["-s", target.toString, link.toString] }
      if out.exitCode != 0 then throw (IO.userError s!"ln failed: {out.stderr}")
    ln outside (root / "escape")
    ln (root / "inner.txt") (root / "self")
    ln (outside / "new.txt") (root / "dangling")
    assertTrue "the lexical rule accepts the path through the symlink"
      (Files.safeRelPath "escape/secret.txt")
    assertTrue "confine refuses a symlink out of the sandbox"
      ((← Files.confine root "escape/secret.txt").isNone)
    assertTrue "a symlink out of the sandbox is refused on read"
      ((← Files.readFileIn root "escape/secret.txt").startsWith "read_file: unsafe")
    assertTrue "a symlink out of the sandbox is refused on list"
      ((← Files.listDirIn root "escape").startsWith "list_dir: unsafe")
    assertTrue "a symlink out of the sandbox is refused on write"
      ((← Files.writeFileIn root "escape/pwned.txt" "x").startsWith "write_file: unsafe")
    assertTrue "a dangling symlink is not written through"
      ((← Files.writeFileIn root "dangling" "x").startsWith "write_file: unsafe")
    assertTrue "nothing was written outside the sandbox"
      (!(← (outside / "pwned.txt").pathExists) && !(← (outside / "new.txt").pathExists))
    assertTrue "a symlink that stays inside the sandbox still reads"
      ((← Files.readFileIn root "self") == "inner")
    assertTrue "a new file under a new directory still writes"
      ((← Files.writeFileIn root "sub/new.txt" "y").startsWith "wrote" &&
        (← IO.FS.readFile (root / "sub" / "new.txt")) == "y")
    let sb : Build.Sandbox := { root, timeoutSecs := 10 }
    let viaLink ← Build.lakeBuild sb "escape" "default"
    assertTrue "a builder project reached through a symlink out of the sandbox is refused"
      (!viaLink.ok && (viaLink.output.splitOn "outside").length > 1)
  let (slow, timedOut) ← Verify.runBounded
    { cmd := "sh", args := #["-c", "echo start; sleep 5; echo end"] } 1
  assertTrue "runBounded stops a process past its deadline"
    (timedOut && slow.stdout.contains "start" && !slow.stdout.contains "end")
  let (quick, quickTimedOut) ← Verify.runBounded { cmd := "sh", args := #["-c", "echo done; exit 3"] } 5
  assertTrue "runBounded returns a finished process's output and exit code"
    (!quickTimedOut && quick.exitCode == 3 && quick.stdout.contains "done")
  -- The process tree. A grandchild orphaned by a subshell is no longer anyone's
  -- direct child, so a parent-based kill never reaches it; it inherits the stdout
  -- pipe and keeps writing a heartbeat. The group kill must stop it, and the call
  -- must return without waiting for the pipe to close.
  IO.FS.withTempDir fun dir => do
    let hb := dir / "heartbeat"
    let script := s!"(while :; do date +%s > {hb}; sleep 0.2; done &); sleep 60; echo end"
    let t0 ← IO.monoMsNow
    let (orphaned, orphanTimedOut) ← Verify.runBounded { cmd := "sh", args := #["-c", script] } 1
    let elapsed := (← IO.monoMsNow) - t0
    assertTrue "runBounded returns within the deadline plus grace with an orphan on the pipe"
      (orphanTimedOut && elapsed < 10000 && !orphaned.stdout.contains "end")
    IO.sleep 700
    let beat1 ← IO.FS.readFile hb
    IO.sleep 700
    let beat2 ← IO.FS.readFile hb
    assertTrue "the orphaned grandchild was killed with its group" (beat1 == beat2)
  -- A child that exits at once but leaves a descendant holding the pipe: the
  -- call still returns, with the child's output, and the descendant is killed.
  IO.FS.withTempDir fun dir => do
    let hb := dir / "heartbeat"
    let script := s!"(while :; do date +%s > {hb}; sleep 0.2; done &); echo gone"
    let t0 ← IO.monoMsNow
    let (left, leftTimedOut) ← Verify.runBounded { cmd := "sh", args := #["-c", script] } 1
    let elapsed := (← IO.monoMsNow) - t0
    assertTrue "runBounded returns when a descendant outlives an exited child"
      (leftTimedOut && left.exitCode == 0 && left.stdout.contains "gone" && elapsed < 10000)
    IO.sleep 700
    let beat1 ← IO.FS.readFile hb
    IO.sleep 700
    let beat2 ← IO.FS.readFile hb
    assertTrue "the descendant left behind was killed with its group" (beat1 == beat2)

def main : IO UInt32 := do
  checkImportFirewall
  sandboxTests
  let secret := "sekrit-token-value"
  let args := Curl.argv ollama.chatUrl (some "/tmp/auth.header")
  assertTrue "curl argv omits bearer secret" (!Curl.argvContains args secret)
  assertTrue "curl argv uses header file" (args.contains "@/tmp/auth.header")
  assertTrue "curl argv keeps HTTP error bodies" (args.contains "--fail-with-body")
  let dummySchema := Lean.Json.mkObj [("type", Lean.Json.str "object")]
  let ollamaReq := chatRequest ollama #[{ role := .user, content := "hi" }] dummySchema "requirement"
  let mantleReq := chatRequest bedrockMantle #[{ role := .user, content := "hi" }] dummySchema "requirement"
  assertTrue "provider swap is config, same encoder"
    (match ollamaReq.getObjVal? "response_format", mantleReq.getObjVal? "response_format" with
     | .ok a, .ok b => Lean.Json.compress a == Lean.Json.compress b
     | _, _ => false)
  assertTrue "namedProvider selects mantle"
    (match namedProvider "bedrock-mantle" with
     | .ok c => c.providerId == "bedrock-mantle" && c.apiKeyEnv == some "AWS_BEARER_TOKEN_BEDROCK"
     | .error _ => false)
  assertTrue "namedProvider rejects unknown ids"
    (match namedProvider "langchain" with
     | .error d => d.contains "langchain"
     | .ok _ => false)
  assertTrue "overlay keeps mantle URL and swaps model"
    (let c := overlayConfig bedrockMantle (some "eu.amazon.nova-lite-v1:0") none
     c.chatUrl == bedrockMantle.chatUrl && c.model == "eu.amazon.nova-lite-v1:0")
  assertTrue "overlay can retarget a second local OpenAI-compat host"
    (let c := overlayConfig ollama none (some "http://127.0.0.1:11435/v1")
     c.chatUrl == "http://127.0.0.1:11435/v1/chat/completions" && c.apiKeyEnv.isNone)
  assertTrue "namedProvider selects openai"
    (match namedProvider "openai" with
     | .ok c =>
       c.providerId == "openai" && c.apiKeyEnv == some "OPENAI_API_KEY" &&
         c.protocol == Protocol.openAIChat
     | .error _ => false)
  assertTrue "namedProvider selects anthropic"
    (match namedProvider "anthropic" with
     | .ok c =>
       c.providerId == "anthropic" && c.apiKeyEnv == some "ANTHROPIC_API_KEY" &&
         c.protocol == Protocol.anthropicMessages &&
         c.chatUrl.endsWith "/v1/messages"
     | .error _ => false)
  assertTrue "namedProvider selects glm"
    (match namedProvider "glm" with
     | .ok c => c.providerId == "glm" && c.apiKeyEnv == some "GLM_API_KEY"
     | .error _ => false)
  assertTrue "ollama config cannot carry an API key env"
    (ollama.apiKeyEnv.isNone &&
      match ollama.authHeader with
      | .none => true
      | .bearer _ | .anthropic _ => false)
  assertTrue "anthropic ping is messages, not chat completions"
    (let b := Lean.Json.compress (pingRequest anthropic)
     b.contains "claude-sonnet-4-5" && !b.contains "chat/completions")
  assertTrue "anthropic extract omits response_format"
    (let dummySchema := Lean.Json.mkObj [("type", Lean.Json.str "object")]
     let b := Lean.Json.compress
       (chatRequest anthropic #[{ role := .user, content := "hi" }] dummySchema "requirement")
     b.contains "max_tokens" && b.contains "matching this schema" &&
       !b.contains "response_format" && !b.contains "json_schema")
  assertTrue "anthropic ask uses input_schema tools"
    (let b := Lean.Json.compress
       (chatRequestTools anthropic #[{ role := .user, content := "hi" }] demoToolSpecs)
     b.contains "input_schema" && !b.contains "parallel_tool_calls")
  assertTrue "anthropic tool_use decodes in the kernel"
    (match stepFromCompletionWith kernelTools
        (wrapAnthropicToolUse "c1" "echo" "{\"text\":\"hi\"}") Protocol.anthropicMessages with
     | .ok s => dispatch s == "hi"
     | .error _ => false)
  assertTrue "anthropic invented tool name refuses"
    (match stepFromCompletionWith kernelTools
        (wrapAnthropicToolUse "c3" "shell" "{\"cmd\":\"rm\"}") Protocol.anthropicMessages with
     | .error (.invalidTag "tool" "name" "shell") => true
     | _ => false)
  assertTrue "anthropic text envelope decodes"
    (match messageContent (wrapAnthropicText "pong") Protocol.anthropicMessages with
     | .ok "pong" => true
     | _ => false)
  assertTrue "audit default belongs to lean-agent"
    (defaultAuditDir.toString == ".lean-agent-audit")
  assertTrue "echo tool executes"
    (match stepFromCompletion (wrapToolCall "c1" "echo" "{\"text\":\"hi\"}") with
     | .ok s => dispatch s == "hi"
     | .error _ => false)
  assertTrue "show is not a kernel tool"
    (match stepFromCompletion (wrapToolCall "c2" "show" "{\"name\":\"theme.selection\"}") with
     | .error (.invalidTag "tool" "name" "show") => true
     | _ => false)
  assertTrue "invented tool name refuses and does not execute"
    (match stepFromCompletion (wrapToolCall "c3" "shell" "{\"cmd\":\"rm\"}") with
     | .error (.invalidTag "tool" "name" "shell") => true
     | .ok _ => false
     | .error _ => false)
  assertTrue "echo extra arg fails closed"
    (match stepFromCompletion (wrapToolCall "c4" "echo" "{\"text\":\"hi\",\"extra\":true}") with
     | .error (.unknownFields "tool.echo" ["extra"]) => true
     | _ => false)
  let tooled :=
    chatRequest ollama #[{ role := .user, content := "hi" }] dummySchema "requirement" demoToolSpecs
  assertTrue "request offers the closed kernel catalog"
    (match tooled.getObjVal? "tools" with
     | .ok t =>
       let s := Lean.Json.compress t
       s.contains "echo" && s.contains "arxiv_search" &&
         !s.contains "\"name\":\"show\"" && !s.contains "\"name\":\"search\"" &&
         !s.contains "\"name\":\"list_catalog\"" &&
         !s.contains "\"name\":\"show_skillset\"" && !s.contains "shell"
     | .error _ => false)
  let pingBody := Lean.Json.compress (pingRequest ollama)
  assertTrue "ping request has no bearer" (!pingBody.contains "Bearer")
  assertTrue "ping request names the model" (pingBody.contains ollama.model)
  assertTrue "ping request uses provider max_tokens"
    (pingBody.contains "\"max_tokens\":1024" && !pingBody.contains "\"max_tokens\":32")
  assertTrue "curl argv sets a timeout" (args.contains "-m")
  match stepFromCompletion (wrapToolCall "c1" "echo" "{\"text\":\"hi\"}") with
  | .error _ =>
      assertTrue "receipt from echo step" false
  | .ok step => do
      let t := receipt ollama step
      let jsonl := encodeJsonl t
      assertTrue "transcript has no bearer" (!jsonl.contains "Bearer")
      assertTrue "transcript roundtrip"
        (match decodeJsonl jsonl with
         | .ok t2 => encodeJsonl t2 == jsonl
         | .error _ => false)
      assertTrue "replay without the model"
        (match replay t with
         | .ok out => out == "hi"
         | .error _ => false)
      -- Replay's own check, on the pre-digest form (no header digest to trip first).
      let tampered := (canonicalJsonl t).replace "\"output\":\"hi\"" "\"output\":\"nope\""
      assertTrue "tampered result fails replay"
        (match decodeJsonl tampered with
         | .ok t2 =>
           match replay t2 with
           | .error (.illFormed "transcript.result" _) => true
           | _ => false
         | .error _ => false)
      -- With the digest in the header the same edit is refused before replay.
      let tamperedDigested := jsonl.replace "\"output\":\"hi\"" "\"output\":\"nope\""
      assertTrue "tampered result fails the digest at decode"
        (match decodeJsonl tamperedDigested with
         | .error (.illFormed "header.digest" "mismatch") => true
         | _ => false)
  let shellLine :=
    "{\"tag\":\"header\",\"runId\":\"run-x\",\"kind\":\"ask\",\"prompt\":\"p\",\"providerId\":\"ollama\",\"model\":\"x\",\"toolsOffered\":[\"echo\"],\"spec\":null}\n" ++
      "{\"tag\":\"invoke\",\"callId\":\"c\",\"tool\":{\"tag\":\"shell\",\"cmd\":\"rm\"}}\n" ++
      "{\"tag\":\"stop\",\"reason\":\"finished\"}"
  assertTrue "forged shell tool cannot enter a transcript"
    (match decodeJsonl shellLine with
     | .error (.invalidTag "tool" "tag" "shell") => true
     | _ => false)
  assertTrue "arxiv_search decodes"
    (match stepFromCompletion (wrapToolCall "c5" "arxiv_search" "{\"query\":\"lean 4\"}") with
     | .ok (.invoke "c5" (.arxivSearch "lean 4")) => true
     | _ => false)
  assertTrue "arxiv GET argv has User-Agent and no POST"
    (let g := Curl.getArgv "https://export.arxiv.org/api/query"
     Curl.argvContains g "lean-agent" && g.contains "-m" && g.contains "-A" && !g.contains "-X")
  let xml :=
    "<feed><title>feed</title><entry><id>http://arxiv.org/abs/2401.00001</id>" ++
      "<title>Lean Demo</title><summary>A paper.</summary></entry></feed>"
  assertTrue "arxiv Atom fixture parses"
    (match (Arxiv.parseEntries xml)[0]? with
     | some h => h.title == "Lean Demo" && h.id.contains "2401.00001"
     | none => false)
  let observed := "http://arxiv.org/abs/2401.00001\nLean Demo\nA paper."
  let arxivT : Transcript := {
    runId := "run-arxiv"
    kind := .ask
    prompt := "find lean 4 papers"
    providerId := "ollama"
    model := "x"
    toolsOffered := #["arxiv_search"]
    events := #[
      .invoke "c1" (.arxivSearch "lean 4"),
      .result "c1" observed,
      .finish "See Lean Demo"
    ]
    stop := .finished
  }
  assertTrue "arxiv observation replays without refetch"
    (match replay arxivT with
     | .ok s => s == "See Lean Demo"
     | .error _ => false)
  assertTrue "generation receipt projects transcript metadata"
    (let r := GenerationReceipt.ofTranscript arxivT
     r.runId == "run-arxiv" && r.providerId == "ollama" && r.model == "x" &&
       r.kind == .ask && r.wellFormed)
  assertTrue "blank run id is not a well-formed receipt"
    (!({
      runId := " "
      providerId := "ollama"
      model := "x"
      kind := .extract
    } : GenerationReceipt).wellFormed)
  assertTrue "search is not a kernel tool"
    (match stepFromCompletion (wrapToolCall "c10" "search" "{\"query\":\"solution approach\"}") with
     | .error (.invalidTag "tool" "name" "search") => true
     | _ => false)
  assertTrue "list_catalog is not a kernel tool"
    (match stepFromCompletion (wrapToolCall "c12" "list_catalog" "{}") with
     | .error (.invalidTag "tool" "name" "list_catalog") => true
     | _ => false)
  assertTrue "show_skillset is not a kernel tool"
    (match stepFromCompletion (wrapToolCall "c12c" "show_skillset" "{\"token\":\"spec-change\"}") with
     | .error (.invalidTag "tool" "name" "show_skillset") => true
     | _ => false)
  assertTrue "bool contract extra key fails closed"
    (match boolFlag.accept (Lean.Json.mkObj [
        ("ok", Lean.Json.bool true), ("extra", Lean.Json.bool true)
      ]) with
     | .error (.unknownFields "bool" ["extra"]) => true
     | _ => false)
  assertTrue "bool contract false is not well-formed"
    (match boolFlag.accept (encodeBoolFlag false) with
     | .error (.illFormed "bool" _) => true
     | _ => false)
  assertTrue "bool contract repairs then succeeds"
    (match boolFlag.accept (Lean.Json.mkObj [
        ("ok", Lean.Json.bool true), ("extra", Lean.Json.num 1)
      ]) with
     | .error e =>
       (boolFlag.repairHint e).contains "unknown fields extra" &&
         (match boolFlag.accept (encodeBoolFlag true) with
          | .ok true => true
          | _ => false)
     | .ok _ => false)
  let extraBool := wrapContent "{\"ok\":true,\"extra\":true}"
  let goodBool := wrapContent (Lean.Json.compress (encodeBoolFlag true))
  let replies ← IO.mkRef [extraBool, goodBool]
  let bodies ← IO.mkRef (#[] : Array String)
  let repairing : Completer := {
    post := fun _url body => do
      bodies.modify (·.push body)
      match ← replies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        replies.set rest
        pure (.ok 200 r)
  }
  let repaired ← boolFlag.extract repairing ollama #[{
    role := .user
    content := "flag"
  }] { maxAttempts := 3 } BackoffPolicy.noSleep
  let posted ← bodies.get
  assertTrue "bool extract repairs then succeeds"
    (match repaired with
     | .ok true => true
     | _ => false)
  assertTrue "bool extract used two attempts" (posted.size == 2)
  assertTrue "bool extract sends repair hint"
    (match posted[1]? with
     | some b => b.contains "unknown fields extra"
     | none => false)
  let fixtureRaw ← IO.FS.readFile "fixtures/extract-theme.jsonl"
  assertTrue "extract-theme.jsonl replays"
    (match decodeJsonl fixtureRaw with
     | .ok t =>
       match replay t with
       | .ok s => s == "theme.selection" && t.outputJson?.isSome
       | .error _ => false
     | .error _ => false)
  assertTrue "extract-theme.jsonl is a pre-digest transcript and still decodes"
    (match headerDigest? fixtureRaw with
     | .ok none => true
     | _ => false)
  -- SHA-256 itself, against FIPS 180-4 vectors, then the digested fixture: it
  -- pins the canonical form, so a change to the encoding is caught here.
  assertTrue "sha256 test vectors"
    (Sha256.hexOfString "abc" == "ba7816bf8f01cfea414140de5dae2223b00361a396177a9cb410ff61f20015ad" &&
      Sha256.hexOfString "" == "e3b0c44298fc1c149afbf4c8996fb92427ae41e4649b934ca495991b7852b855")
  let digestedRaw ← IO.FS.readFile "fixtures/digested-ask.jsonl"
  assertTrue "digested-ask.jsonl decodes with its digest verified and replays"
    (match decodeJsonl digestedRaw with
     | .ok t =>
       (match replay t with
        | .ok s => s == "lean"
        | .error _ => false) &&
         (match headerDigest? digestedRaw with
          | .ok (some d) => d == digest t
          | _ => false)
     | .error _ => false)
  assertTrue "digested-ask.jsonl pins the canonical form"
    (match headerDigest? digestedRaw with
     | .ok (some d) => d == "sha256:96c11ad350c7770316ad5c565e4fa33c9e3f6f9fe5daabb0add4638ddbce2a7e"
     | _ => false)
  let observed := "http://arxiv.org/abs/2401.00001\nLean Demo\nA paper."
  let askReplies ← IO.mkRef [
    wrapToolCall "c1" "arxiv_search" "{\"query\":\"lean 4\"}",
    wrapContent "Found Lean Demo (http://arxiv.org/abs/2401.00001)."
  ]
  let askBodies ← IO.mkRef (#[] : Array String)
  let asking : Completer := {
    post := fun _url body => do
      askBodies.modify (·.push body)
      match ← askReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        askReplies.set rest
        pure (.ok 200 r)
  }
  let asked ← ask asking ollama defaultAskPrompt {} (stubArxivRunner observed) "run-ask"
  let askedBodies ← askBodies.get
  assertTrue "ask loop uses the tool then finishes"
    (asked.stop == .finished &&
      asked.kind == .ask &&
      asked.prompt == defaultAskPrompt &&
      finishText asked == some "Found Lean Demo (http://arxiv.org/abs/2401.00001)." &&
      (encodeJsonl asked).contains defaultAskPrompt &&
      !(encodeJsonl asked).contains "Bearer" &&
      (match replay asked with
       | .ok s => s == "Found Lean Demo (http://arxiv.org/abs/2401.00001)."
       | .error _ => false))
  assertTrue "ask does not force requirement json_schema"
    (match askedBodies[0]? with
     | some b =>
       b.contains "arxiv_search" && !b.contains "response_format" && !b.contains "Bearer"
     | none => false)
  assertTrue "ask second turn carries the tool result"
    (match askedBodies[1]? with
     | some b => b.contains "tool_call_id" && b.contains "Lean Demo"
     | none => false)
  -- One loop, several calls. An OpenAI Chat turn with two calls runs both in the
  -- model's order and posts one assistant message carrying both calls, then one
  -- tool message per call.
  let twoReplies ← IO.mkRef [twoEchoCalls, wrapContent "a then b"]
  let twoBodies ← IO.mkRef (#[] : Array String)
  let twoCalling : Completer := {
    post := fun _url body => do
      twoBodies.modify (·.push body)
      match ← twoReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        twoReplies.set rest
        pure (.ok 200 r)
  }
  let twoCalled ← ask twoCalling ollama "echo a and b" {} (stubArxivRunner observed) "run-two-calls"
  let twoPosted ← twoBodies.get
  assertTrue "a two-call turn runs both calls in order, then finishes"
    (twoCalled.stop == .finished &&
      twoCalled.events == #[.invoke "c1" (.echo "a"), .result "c1" "a",
        .invoke "c2" (.echo "b"), .result "c2" "b", .finish "a then b"] &&
      twoCalled.wellFormed &&
      (match replay twoCalled with
       | .ok s => s == "a then b"
       | .error _ => false))
  let messagesOf (body : String) : Array Lean.Json :=
    match Lean.Json.parse body with
    | .ok j => ((j.getObjVal? "messages").toOption.bind (·.getArr?.toOption)).getD #[]
    | .error _ => #[]
  let roleIs (m : Lean.Json) (role : String) : Bool :=
    (m.getObjValAs? String "role").toOption == some role
  assertTrue "the second request has one assistant message with both calls and a tool message per call"
    (match twoPosted[1]? with
     | some b =>
       let ms := messagesOf b
       (ms.filter (roleIs · "assistant")).size == 1 &&
         (ms.filter (roleIs · "tool")).size == 2 &&
         (ms.any fun m => roleIs m "assistant" &&
           ((m.getObjVal? "tool_calls").toOption.bind (·.getArr?.toOption)).map (·.size) == some 2) &&
         b.contains "\"tool_call_id\":\"c1\"" && b.contains "\"tool_call_id\":\"c2\""
     | none => false)
  -- The same turn in the Anthropic Messages protocol: two `tool_use` blocks in,
  -- two `tool_result` blocks back.
  let twoUses := wrapAnthropicToolUses #[("t1", "echo", "{\"text\":\"a\"}"), ("t2", "echo", "{\"text\":\"b\"}")]
  let anthReplies ← IO.mkRef [twoUses, wrapAnthropicText "a then b"]
  let anthBodies ← IO.mkRef (#[] : Array String)
  let anthCalling : Completer := {
    post := fun _url body => do
      anthBodies.modify (·.push body)
      match ← anthReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        anthReplies.set rest
        pure (.ok 200 r)
  }
  let anthCalled ← ask anthCalling anthropic "echo a and b" {} (stubArxivRunner observed) "run-two-uses"
  let anthPosted ← anthBodies.get
  assertTrue "anthropic: a two-tool_use turn runs both calls in order, then finishes"
    (anthCalled.stop == .finished &&
      anthCalled.events == #[.invoke "t1" (.echo "a"), .result "t1" "a",
        .invoke "t2" (.echo "b"), .result "t2" "b", .finish "a then b"] &&
      anthCalled.wellFormed)
  assertTrue "anthropic: the second request echoes both tool_use blocks and answers each"
    (match anthPosted[1]? with
     | some b =>
       (b.splitOn "\"type\":\"tool_use\"").length == 3 &&
         b.contains "\"tool_use_id\":\"t1\"" && b.contains "\"tool_use_id\":\"t2\"" &&
         !b.contains "Bearer"
     | none => false)
  -- One invented name in a multi-call turn refuses the whole turn; the echo beside
  -- it does not run.
  let mixed : Completer := {
    post := fun _url _body =>
      pure (.ok 200 (wrapToolCalls #[("c1", "echo", "{\"text\":\"a\"}"), ("c2", "shell", "{\"cmd\":\"rm\"}")]))
  }
  let mixedRun ← ask mixed ollama "echo and shell" { maxTurns := 2 } (stubArxivRunner observed) "run-mixed"
  assertTrue "a multi-call turn with an invented name refuses without running anything"
    (mixedRun.stop == .refused 1 &&
      mixedRun.events.all (fun e =>
        match e with
        | .repair _ d => d.contains "shell"
        | _ => false))
  -- A throwing runner is that call's result, and the turn's other call still runs.
  let throwing : ToolRunner DemoTool := {
    run := fun t =>
      match t with
      | .echo "a" => throw (IO.userError "disk on fire")
      | .echo text => pure text
      | .arxivSearch _ => pure observed
  }
  let throwReplies ← IO.mkRef [twoEchoCalls, wrapContent "coped"]
  let throwC : Completer := {
    post := fun _url _body => do
      match ← throwReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        throwReplies.set rest
        pure (.ok 200 r)
  }
  let coped ← ask throwC ollama "echo a and b" {} throwing "run-throwing-runner"
  assertTrue "a throwing runner becomes that call's result and the receipt survives"
    (coped.stop == .finished &&
      (match coped.events[1]? with
       | some (Event.result "c1" out) => out.contains "disk on fire" && out.startsWith "echo error"
       | _ => false) &&
      coped.events[3]? == some (.result "c2" "b"))
  -- The finish gate: the first finish is nudged (a repair event, and the reply is
  -- the next user message in the same history); the second is accepted.
  let gateReplies ← IO.mkRef [wrapContent "early", wrapContent "final"]
  let gateBodies ← IO.mkRef (#[] : Array String)
  let gating : Completer := {
    post := fun _url body => do
      gateBodies.modify (·.push body)
      match ← gateReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        gateReplies.set rest
        pure (.ok 200 r)
  }
  let oncePolicy : AskPolicy DemoTool := {
    onFinish := some fun info =>
      pure (if info.nudges == 0 then .nudge "not yet" "keep going" else .accept)
  }
  let gated ← ask gating ollama "finish twice" oncePolicy (stubArxivRunner observed) "run-gate"
  let gatePosted ← gateBodies.get
  assertTrue "a nudged finish is a repair event; the next finish is accepted"
    (gated.stop == .finished &&
      finishText gated == some "final" &&
      gated.events == #[.repair 1 "not yet", .finish "final"] &&
      gated.wellFormed)
  assertTrue "the nudge reply and the nudged finish reach the model in the same history"
    (match gatePosted[1]? with
     | some b => b.contains "keep going" && b.contains "early" && b.contains "finish twice"
     | none => false)
  let early : Completer := { post := fun _url _body => pure (.ok 200 (wrapContent "early")) }
  let stubbornPolicy : AskPolicy DemoTool := {
    maxTurns := 2
    onFinish := some fun _ => pure (.nudge "not yet" "keep going")
  }
  let stubborn ← ask early ollama "never done" stubbornPolicy (stubArxivRunner observed) "run-stubborn"
  assertTrue "a gate that never accepts is bounded by maxTurns and refuses"
    (stubborn.stop == .refused 2 &&
      stubborn.events == #[.repair 1 "not yet", .repair 2 "not yet"] &&
      stubborn.wellFormed)
  let crashingPolicy : AskPolicy DemoTool := {
    onFinish := some fun _ => throw (IO.userError "gate crashed")
  }
  let crashed ← ask early ollama "finish" crashingPolicy (stubArxivRunner observed) "run-gate-crash"
  assertTrue "a throwing gate refuses with a receipt"
    (crashed.stop == .refused 1 &&
      (lastRepairDetail crashed).map (·.contains "gate crashed") == some true)
  let blankNudgePolicy : AskPolicy DemoTool := {
    onFinish := some fun _ => pure (.nudge "not yet" "   ")
  }
  let blankNudged ← ask early ollama "finish" blankNudgePolicy (stubArxivRunner observed) "run-blank-nudge"
  assertTrue "a blank nudge reply refuses instead of sending a blank message"
    (blankNudged.stop == .refused 1 && lastRepairDetail blankNudged == some "blank nudge reply")
  let shelling : Completer := {
    post := fun _url _body =>
      pure (.ok 200 (wrapToolCall "c9" "shell" "{\"cmd\":\"rm\"}"))
  }
  let invented2 ← ask shelling ollama "run a shell" { maxTurns := 2 }
    (stubArxivRunner observed) "run-shell"
  assertTrue "ask refuses invented tool names and keeps a receipt"
    (invented2.stop == .refused 1 &&
      invented2.prompt == "run a shell" &&
      invented2.events.any (fun e =>
        match e with
        | .repair _ d => d.contains "shell"
        | .invoke _ _ => false
        | .result _ _ => false
        | .reasoning _ _ => false
        | .finish _ => false))
  let dying : Completer := {
    post := fun _url _body => pure (.err { body := "connection refused" })
  }
  let transported ← ask dying ollama "hello" { maxTurns := 2 }
    (stubArxivRunner observed) "run-transport" BackoffPolicy.noSleep
  assertTrue "ask transport still yields a receipt"
    (transported.stop == .transport &&
      transported.prompt == "hello" &&
      lastRepairDetail transported == some "connection refused")
  assertTrue "openai truncated finish_reason is a typed stop"
    (match messageContent (wrapContentTruncated "{\"id\":\"x\"}") with
     | .error (.illFormed "completion" "truncated") => true
     | _ => false)
  assertTrue "anthropic max_tokens is truncated"
    (match messageContent (wrapAnthropicTruncated "partial") Protocol.anthropicMessages with
     | .error (.illFormed "completion" "truncated") => true
     | _ => false)
  let truncating : Completer := {
    post := fun _url _body => pure (.ok 200 (wrapContentTruncated "{\"ok\":true}"))
  }
  let truncated ← boolFlag.extract truncating ollama #[{ role := .user, content := "flag" }]
    { maxAttempts := 2 } BackoffPolicy.noSleep
  assertTrue "extract truncation is fatal"
    (match truncated with
     | .error .truncated => ExtractError.classify .truncated == FailureClass.fatal
     | _ => false)
  let rateLimit := "{\"error\":{\"type\":\"rate_limit_error\",\"message\":\"slow down\"}}"
  let rateBodies ← IO.mkRef (#[] : Array String)
  let rateReplies ← IO.mkRef [
    (Sum.inl rateLimit : Sum String String),
    Sum.inr (wrapContent (Lean.Json.compress (encodeBoolFlag true)))
  ]
  let rateLimiting : Completer := {
    post := fun _url body => do
      rateBodies.modify (·.push body)
      match ← rateReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        rateReplies.set rest
        match r with
        | .inl d => pure (.err { body := d })
        | .inr ok => pure (.ok 200 ok)
  }
  let recovered ← boolFlag.extract rateLimiting ollama #[{ role := .user, content := "flag" }]
    { maxAttempts := 3 } BackoffPolicy.noSleep
  let ratePosted ← rateBodies.get
  assertTrue "extract retries rate_limit_error"
    (match recovered with
     | .ok true => ratePosted.size == 2
     | _ => false)
  let authFail := "{\"error\":{\"type\":\"authentication_error\",\"message\":\"bad key\"}}"
  let fatalAuth : Completer := {
    post := fun _url _body => pure (.err { body := authFail })
  }
  let auth ← boolFlag.extract fatalAuth ollama #[{ role := .user, content := "flag" }]
    { maxAttempts := 3 } BackoffPolicy.noSleep
  assertTrue "extract does not retry authentication_error"
    (match auth with
     | .error (.provider "authentication_error" "bad key") =>
       ExtractError.classify (.provider "authentication_error" "bad key") == FailureClass.fatal
     | _ => false)
  IO.FS.withTempDir fun dir => do
    match ← writeAudit dir invented2 with
    | .error _ =>
        assertTrue "write refused ask audit" false
    | .ok path => do
        let raw ← IO.FS.readFile path
        assertTrue "refused ask audit has prompt" (raw.contains "run a shell")
        assertTrue "refused ask audit has no bearer" (!raw.contains "Bearer")
  -- Traceability: prompt, model reasoning, and final output are all preserved
  -- in the audit transcript. Reasoning is audit-only (never re-sent, never
  -- treated as output, ignored by replay).
  let reasoningReply :=
    wrapContentReasoning
      "The user wants Lean 4 papers; I already know one, so I will answer directly."
      "Lean Demo is a relevant paper."
  let reasoningCompleter : Completer := {
    post := fun _url _body => pure (.ok 200 reasoningReply)
  }
  let reasoned ← ask reasoningCompleter ollama "find lean 4 papers" {}
    (stubArxivRunner observed) "run-reasoning"
  let reasonedJsonl := encodeJsonl reasoned
  assertTrue "ask finishes and records the final output"
    (reasoned.stop == .finished &&
      finishText reasoned == some "Lean Demo is a relevant paper.")
  assertTrue "reasoning is captured as an audit event"
    (reasoned.events.any (fun e =>
      match e with
      | .reasoning _ c => c.contains "answer directly"
      | .invoke _ _ => false
      | .result _ _ => false
      | .repair _ _ => false
      | .finish _ => false))
  assertTrue "audit preserves prompt, reasoning, and output together"
    (reasonedJsonl.contains "find lean 4 papers" &&
      reasonedJsonl.contains "answer directly" &&
      reasonedJsonl.contains "Lean Demo is a relevant paper." &&
      !reasonedJsonl.contains "Bearer")
  assertTrue "reasoning survives a JSONL roundtrip"
    (match decodeJsonl reasonedJsonl with
     | .ok t2 => t2.events == reasoned.events && encodeJsonl t2 == reasonedJsonl
     | .error _ => false)
  assertTrue "reasoning is ignored by replay (audit-only, not output)"
    (match replay reasoned with
     | .ok s => s == "Lean Demo is a relevant paper."
     | .error _ => false)
  -- Reasoning is a trace, never fed back to the model as an input turn: in a
  -- two-turn run the second request body carries the tool call and its result
  -- but not the first turn's reasoning.
  let thought := "I should search arXiv before answering."
  let toolCallWithReasoning := Lean.Json.compress (Lean.Json.mkObj [
    ("choices", Lean.Json.arr #[Lean.Json.mkObj [
      ("finish_reason", Lean.Json.str "tool_calls"),
      ("message", Lean.Json.mkObj [
        ("role", Lean.Json.str "assistant"),
        ("content", Lean.Json.null),
        ("reasoning_content", Lean.Json.str thought),
        ("tool_calls", Lean.Json.arr #[Lean.Json.mkObj [
          ("id", Lean.Json.str "c1"),
          ("type", Lean.Json.str "function"),
          ("function", Lean.Json.mkObj [
            ("name", Lean.Json.str "arxiv_search"),
            ("arguments", Lean.Json.str "{\"query\":\"lean 4\"}")
          ])
        ]])
      ])
    ]])
  ])
  let twoTurnReplies ← IO.mkRef [toolCallWithReasoning, wrapContent "Lean Demo is relevant."]
  let twoTurnBodies ← IO.mkRef (#[] : Array String)
  let twoTurnCompleter : Completer := {
    post := fun _url body => do
      twoTurnBodies.modify (·.push body)
      match ← twoTurnReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        twoTurnReplies.set rest
        pure (.ok 200 r)
  }
  let twoTurn ← ask twoTurnCompleter ollama "find lean 4 papers" {}
    (stubArxivRunner observed) "run-reasoning-2"
  let twoTurnPosted ← twoTurnBodies.get
  assertTrue "reasoning before a tool call is recorded"
    (twoTurn.stop == .finished &&
      twoTurn.events.any (fun e =>
        match e with
        | .reasoning 1 c => c == thought
        | _ => false))
  assertTrue "reasoning is not sent back to the provider"
    (twoTurnPosted.size == 2 &&
      (match twoTurnPosted[1]? with
       | some b => b.contains "Lean Demo" && b.contains "tool_call_id" && !b.contains thought
       | none => false))
  -- A runner that throws does not lose the receipt: the exception is the tool's
  -- result, the loop goes on, and the transcript still writes.
  let throwingRunner : ToolRunner DemoTool := {
    run := fun t =>
      match t with
      | .echo text => pure text
      | .arxivSearch _ => throw (IO.userError "arxiv exploded")
  }
  let throwReplies ← IO.mkRef [
    wrapToolCall "c1" "arxiv_search" "{\"query\":\"lean 4\"}",
    wrapContent "The search failed, so I cannot cite a paper."
  ]
  let throwingCompleter : Completer := {
    post := fun _url _body => do
      match ← throwReplies.get with
      | [] => pure (.err { body := "script exhausted" })
      | r :: rest =>
        throwReplies.set rest
        pure (.ok 200 r)
  }
  let thrown ← ask throwingCompleter ollama "find lean 4 papers" {} throwingRunner "run-throw"
  assertTrue "a throwing runner becomes a tool-error result"
    (thrown.stop == .finished &&
      thrown.events.any (fun e =>
        match e with
        | .result "c1" out => out.contains "arxiv_search error" && out.contains "arxiv exploded"
        | _ => false))
  IO.FS.withTempDir fun dir => do
    match ← writeAudit dir thrown with
    | .error _ => assertTrue "write audit after a throwing runner" false
    | .ok path => do
        let raw ← IO.FS.readFile path
        assertTrue "audit after a throwing runner carries the error"
          (raw.contains "arxiv exploded" && raw.contains "\"reason\":\"finished\"")
  IO.FS.withTempDir fun dir => do
    match ← writeAudit dir reasoned with
    | .error _ => assertTrue "write reasoning audit" false
    | .ok path => do
        let raw ← IO.FS.readFile path
        assertTrue "persisted audit carries the model reasoning"
          (raw.contains "answer directly" && raw.contains "\"tag\":\"reasoning\"")
        -- Content digest: the written audit round-trips with its digest verified,
        -- and an edit to model free text (finish or reasoning) in the file is
        -- refused by the decoder, which replay alone could not detect.
        assertTrue "written audit carries a sha256 content digest"
          (match headerDigest? raw with
           | .ok (some d) => d == digest reasoned && d.startsWith "sha256:" && d.length == 7 + 64
           | _ => false)
        assertTrue "written audit decodes with its digest verified"
          (match decodeJsonl raw with
           | .ok t2 => t2.events == reasoned.events && digest t2 == digest reasoned
           | .error _ => false)
        let forgedFinish := raw.replace "Lean Demo is a relevant paper." "Lean Demo is not relevant."
        IO.FS.writeFile path forgedFinish
        let reread ← IO.FS.readFile path
        assertTrue "an edited finish line in the audit file is refused"
          (reread != raw &&
            (match decodeJsonl reread with
             | .error (.illFormed "header.digest" "mismatch") => true
             | _ => false))
        let forgedReasoning := raw.replace "answer directly" "answer later"
        assertTrue "an edited reasoning line is refused"
          (forgedReasoning != raw &&
            (match decodeJsonl forgedReasoning with
             | .error (.illFormed "header.digest" "mismatch") => true
             | _ => false))
        let badAlgo := raw.replace "\"digest\":\"sha256:" "\"digest\":\"md5:"
        assertTrue "an unknown digest algorithm is refused"
          (match decodeJsonl badAlgo with
           | .error (.illFormed "header.digest" "unsupported algorithm") => true
           | _ => false)
        -- Stripping the digest yields the pre-digest form, which still decodes
        -- under the default policy and is refused under `.require`: so is a file
        -- whose finish was edited and whose digest was then deleted.
        assertTrue "the canonical (pre-digest) form still decodes"
          (match decodeJsonl (canonicalJsonl reasoned) with
           | .ok t2 => t2.events == reasoned.events
           | .error _ => false)
        assertTrue "a missing digest is refused when one is required"
          (match decodeJsonl (canonicalJsonl reasoned) .require with
           | .error (.illFormed "header.digest" "missing") => true
           | _ => false)
        let stripped := forgedFinish.replace ("\"digest\":\"" ++ digest reasoned ++ "\",") ""
        assertTrue "an edited finish with the digest deleted is refused when one is required"
          (!stripped.contains "digest" &&
            (match decodeJsonl stripped .require with
             | .error (.illFormed "header.digest" "missing") => true
             | _ => false))
        assertTrue "a present digest is still verified when one is required"
          (match decodeJsonl raw .require with
           | .ok t2 => t2.events == reasoned.events
           | .error _ => false)
        -- The usage object is under the same fail-closed rule as the header:
        -- a key or value the encoder never writes is refused, not ignored.
        let header := (jsonlLines raw).head!
        let withUsage (u : String) : String :=
          raw.replace header (header.replace "\"spec\":null" ("\"spec\":null,\"usage\":" ++ u))
        assertTrue "a usage object with an unknown key is refused"
          (match decodeJsonl (withUsage "{\"note\":\"edited\"}") with
           | .error (.unknownFields "header.usage" ["note"]) => true
           | _ => false)
        assertTrue "a usage value that is not an object is refused"
          (match decodeJsonl (withUsage "\"hello\"") with
           | .error (.expectedObject "header.usage") => true
           | _ => false)
        assertTrue "a usage count that is not a number is refused"
          (match decodeJsonl (withUsage "{\"promptTokens\":\"12\"}") with
           | .error (.wrongType "header.usage" "promptTokens" _) => true
           | _ => false)
  -- Token usage: parsed from the provider envelope, summed over turns, persisted.
  let usageReply :=
    "{\"choices\":[{\"finish_reason\":\"stop\",\"message\":{\"role\":\"assistant\"," ++
      "\"content\":\"done\"}}],\"usage\":{\"prompt_tokens\":12,\"completion_tokens\":8," ++
      "\"total_tokens\":20}}"
  let usageCompleter : Completer := {
    post := fun _url _body => pure (.ok 200 usageReply)
  }
  let usaged ← ask usageCompleter ollama "count my tokens" {}
    (stubArxivRunner observed) "run-usage"
  assertTrue "token usage is captured on the transcript"
    (usaged.usage.promptTokens == some 12 &&
      usaged.usage.completionTokens == some 8 &&
      usaged.usage.totalTokens == some 20)
  assertTrue "usage survives a JSONL roundtrip"
    (match decodeJsonl (encodeJsonl usaged) with
     | .ok t2 => t2.usage == usaged.usage
     | .error _ => false)
  assertTrue "generation receipt carries usage"
    ((GenerationReceipt.ofTranscript usaged).usage.totalTokens == some 20)
  assertTrue "a token-less run writes no usage object"
    (!(encodeJsonl reasoned).contains "\"usage\"")
  -- Backoff schedule is exponential and capped; deterministic, so testable.
  assertTrue "backoff delay is exponential"
    (BackoffPolicy.delayMs { jitterMs := 0 } 0 == 250 &&
      BackoffPolicy.delayMs { jitterMs := 0 } 1 == 500 &&
      BackoffPolicy.delayMs { jitterMs := 0 } 2 == 1000)
  assertTrue "backoff delay is capped at maxMs"
    (BackoffPolicy.delayMs { baseMs := 250, maxMs := 800, jitterMs := 0 } 10 == 800)
  -- Run ids resist same-millisecond collisions.
  let id1 ← freshRunId
  let id2 ← freshRunId
  assertTrue "fresh run ids are unique and safe filenames"
    (id1 != id2 && safeRunId id1 && safeRunId id2)
  -- Audit layer as a system of record: atomic write, append-only index,
  -- rebuild, and query — all against a temp directory.
  IO.FS.withTempDir fun dir => do
    match ← writeAuditIndexed dir usaged with
    | .error _ => assertTrue "indexed audit write" false
    | .ok _ =>
        -- Atomic write leaves no stray .tmp file behind.
        let tmpLeft ← (⟨dir.toString ++ "/" ++ usaged.runId ++ ".jsonl.tmp"⟩ : System.FilePath).pathExists
        assertTrue "atomic write leaves no .tmp" (!tmpLeft)
        let idx ← readIndex dir
        assertTrue "index records the run with usage"
          (idx.size == 1 &&
            (match idx[0]? with
             | some e => e.runId == usaged.runId && e.usage.totalTokens == some 20 &&
                 e.providerId == "ollama" && AuditEntry.finished e &&
                 e.digest == some (digest usaged)
             | none => false))
    -- Add a second, refused run, then rebuild the index purely from transcripts.
    match ← writeAuditIndexed dir invented2 with
    | .error _ => assertTrue "second indexed audit write" false
    | .ok _ =>
        let rebuilt ← rebuildIndex dir
        assertTrue "rebuild reconstructs the index from transcripts"
          (rebuilt.size == 2)
        assertTrue "rebuilt index rows carry the transcript digests"
          (rebuilt.all fun e => e.digest.isSome)
        assertTrue "query: exactly one refused run"
          ((refusedRuns rebuilt).size == 1)
        assertTrue "query: both runs are on ollama"
          ((byProvider rebuilt "ollama").size == 2)
        assertTrue "query: token totals aggregate across runs"
          (totalTokens rebuilt == 20)
  -- Concurrency: fan-out runs same-role agents in parallel and preserves order.
  let fanMarket := ({
    name := "m", system := "s", cfg := ollama
    tools := Roles.marketTools, runner := Roles.marketRunner
  } : Agent Roles.Market)
  let fanC1 : Completer := { post := fun _ _ => pure (.ok 200 (wrapContent "A")) }
  let fanC2 : Completer := { post := fun _ _ => pure (.ok 200 (wrapContent "B")) }
  let fanResults ← fanOut #[
    fanMarket.run fanC1 "read A" "run-fan-a",
    fanMarket.run fanC2 "read B" "run-fan-b"
  ]
  let fanText (r : Except IO.Error (Transcript Roles.Market)) : Option String :=
    match r with
    | .ok t => finishText t
    | .error _ => none
  assertTrue "fan-out returns both transcripts in order"
    (fanResults.size == 2 &&
      (fanResults[0]?.map fanText == some (some "A")) &&
      (fanResults[1]?.map fanText == some (some "B")))
  -- Typed mailbox: a Lean value crosses between steps as a value, not a string.
  let mbox ← Mailbox.new (α := Nat × String)
  mbox.post (7, "brief")
  let taken ← mbox.take?
  let empty ← mbox.take?
  assertTrue "mailbox round-trips a typed value then empties"
    (taken == some (7, "brief") && empty == none)
  -- Verifier role: off-catalog names cannot inhabit it.
  assertTrue "verifier refuses non-lean tools"
    (match Roles.decodeVerifier "web_search" (Lean.Json.mkObj [("query", Lean.Json.str "x")]) with
     | .error (.invalidTag "tool" "name" "web_search") => true
     | _ => false)
  -- leanCheck actually compiles: accept a good snippet, reject a type error.
  let goodV ← Verify.leanCheck "def n : Nat := 1\n#eval n" 60
  assertTrue "leanCheck accepts a well-typed snippet" goodV.ok
  let badV ← Verify.leanCheck "def n : Nat := \"nope\"" 60
  assertTrue "leanCheck rejects an ill-typed snippet" (!badV.ok)
  builderTests
  IO.println "lean-agent tests passed"
  return 0
