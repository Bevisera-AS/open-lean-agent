import LeanAgent.Util
import LeanAgent.Live
import LeanAgent.Transcript
import LeanAgent.AuditIndex
import LeanAgent.Ask

open LeanAgent

def usage : String :=
  "usage: lean-agent (live-ping | ask [prompt…] | replay-transcript | list-audits)"

def fail (msg : String) : IO UInt32 := do
  IO.eprintln msg
  return 1

def persistAudit (t : Transcript) : IO Unit := do
  let dir ← auditDirFromEnv
  match ← writeAuditIndexed dir t with
  | .ok path => IO.eprintln s!"audit {path}"
  | .error d => IO.eprintln s!"audit not written: {d}"

def withLiveConfig (k : ProviderConfig → IO UInt32) : IO UInt32 := do
  match ← liveConfig with
  | .error d => fail d
  | .ok cfg => k cfg

def main (args : List String) : IO UInt32 := do
  match args with
  | ["live-ping"] =>
      withLiveConfig fun cfg => do
        IO.eprintln s!"live-ping {cfg.providerId} model={cfg.model} url={cfg.chatUrl}"
        match ← livePing cfg with
        | .ok text =>
            IO.println text
            return 0
        | .error e => fail e.pretty
  | "ask" :: rest =>
      let prompt :=
        if rest.isEmpty then defaultAskPrompt else joinSep " " rest
      withLiveConfig fun cfg => do
        IO.eprintln s!"ask {cfg.providerId} model={cfg.model} url={cfg.chatUrl}"
        let t ← liveAsk cfg prompt {}
        persistAudit t
        match t.stop with
        | .finished =>
            match finishText t with
            | some text =>
                IO.println text
                return 0
            | none => fail "ask finished without text"
        | .refused n =>
            let extra := (lastRepairDetail t).map (fun d => s!": {d}") |>.getD ""
            fail s!"refused after {n} attempt(s){extra}"
        | .transport =>
            let extra := (lastRepairDetail t).map (fun d => s!": {d}") |>.getD ""
            fail s!"transport error{extra}"
        | .truncated =>
            fail "truncated"
  | ["list-audits"] => do
      let dir ← auditDirFromEnv
      -- Rebuild from the transcripts so the manifest is authoritative, then print.
      let entries ← rebuildIndex dir
      IO.eprintln s!"{entries.size} run(s) in {dir} — {totalTokens entries} total tokens"
      for e in entries do
        let toks := e.usage.totalTokens.map toString |>.getD "-"
        IO.println s!"{e.runId}\t{e.providerId}\t{e.model}\t{e.kind.toWire}\t{repr e.stop}\ttokens={toks}\t{e.promptPreview}"
      return 0
  | ["replay-transcript"] => do
      let raw ← (← IO.getStdin).readToEnd
      if !nonemptyText raw then
        fail "replay-transcript reads a transcript JSONL on stdin (fixtures/extract-theme.jsonl or .lean-agent-audit/run-*.jsonl)"
      else
        match decodeJsonl raw with
        | .error e => fail e.pretty
        | .ok t =>
            match replay t with
            | .ok out =>
                IO.println out
                return 0
            | .error e => fail e.pretty
  | _ => fail usage
