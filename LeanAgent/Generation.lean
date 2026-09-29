module

public import LeanAgent.Transcript
public meta import LeanAgent.Transcript

namespace LeanAgent

public section

/-- Facts about one model run. Not an identity, not a signature, and not human
accept. Archive remains a separate capability. -/
public structure GenerationReceipt where
  runId : String
  providerId : String
  model : String
  kind : RunKind
  usage : Usage := {}
  deriving Repr, BEq

public def GenerationReceipt.wellFormed (r : GenerationReceipt) : Bool :=
  safeRunId r.runId &&
    nonemptyText r.providerId &&
    nonemptyText r.model

/-- Project run facts from a transcript. Does not copy events or output. -/
public def GenerationReceipt.ofTranscript {Tool : Type} (t : Transcript Tool) :
    GenerationReceipt :=
  { runId := t.runId, providerId := t.providerId, model := t.model, kind := t.kind
    usage := t.usage }

/-- The receipt is exactly the transcript's run metadata, including token usage. -/
public theorem GenerationReceipt.ofTranscript_sound {Tool : Type} (t : Transcript Tool) :
    let r := ofTranscript t
    r.runId = t.runId ∧ r.providerId = t.providerId ∧ r.model = t.model ∧ r.kind = t.kind ∧
      r.usage = t.usage :=
  ⟨rfl, rfl, rfl, rfl, rfl⟩

#guard
  let r : GenerationReceipt := {
    runId := "run-1"
    providerId := "ollama"
    model := "test"
    kind := .extract
  }
  r.wellFormed

#guard
  let r : GenerationReceipt := {
    runId := ""
    providerId := "ollama"
    model := "test"
    kind := .extract
  }
  !r.wellFormed

end

end LeanAgent
