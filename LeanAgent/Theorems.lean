import LeanAgent.Files
import LeanAgent.Tools
import LeanAgent.OutputContract
import LeanAgent.Transcript

/-!
The pure checks as theorems, so `lake check` re-verifies them with the kernel
instead of trusting the interpreter that evaluates a `#guard`.

This file is deliberately not a `module`: inside a module file `decide` cannot
unfold `Lean.Data.Json` (its definitions are not exposed), so nothing that
decodes JSON can be decided there. A legacy import sees every body. The
JSON-free theorems live next to their definitions (`Files.safeRelPath`). Each
statement is the Boolean a `#guard` would evaluate, proved by `decide`; the
replay and schema ones need `decide +kernel` because they fold over arrays and
tree maps, which only the kernel's reduction unfolds.
-/

namespace LeanAgent

open Lean

/-! ## Unknown fields fail closed -/

theorem exactFields_rejects_unknown :
    (match (do
        let o ← asObj "c" (Json.mkObj [("a", Json.str "1"), ("b", Json.str "2")])
        exactFields "c" ["a"] o : Except DecodeError Unit) with
     | .error (.unknownFields "c" ["b"]) => true
     | _ => false) = true := by decide

theorem exactFields_accepts_listed :
    (match (do
        let o ← asObj "c" (Json.mkObj [("a", Json.str "1")])
        exactFields "c" ["a", "b"] o : Except DecodeError Unit) with
     | .ok () => true
     | _ => false) = true := by decide

theorem asObj_rejects_non_object :
    (match asObj "c" (Json.str "x") with
     | .error (.expectedObject "c") => true
     | _ => false) = true := by decide

/-! ## A name outside the catalog never inhabits the tool type -/

theorem decode_echo :
    (match decodeDemoTool "echo" (Json.mkObj [("text", Json.str "hi")]) with
     | .ok t => execute t == "hi"
     | .error _ => false) = true := by decide

theorem decode_rejects_off_catalog :
    (match decodeDemoTool "shell" (Json.mkObj [("cmd", Json.str "rm")]) with
     | .error (.invalidTag "tool" "name" "shell") => true
     | _ => false) = true := by decide

theorem decode_rejects_unknown_field :
    (match decodeDemoTool "echo" (Json.mkObj [("text", Json.str "hi"), ("x", Json.str "y")]) with
     | .error (.unknownFields "tool.echo" ["x"]) => true
     | _ => false) = true := by decide

theorem decode_rejects_blank :
    (match decodeDemoTool "echo" (Json.mkObj [("text", Json.str "  ")]) with
     | .error (.illFormed "tool.echo.text" "blank") => true
     | _ => false) = true := by decide

theorem decodeTagged_rejects_off_catalog :
    (match decodeTaggedDemoTool (Json.mkObj [("tag", Json.str "shell"), ("cmd", Json.str "rm")]) with
     | .error (.invalidTag "tool" "tag" "shell") => true
     | _ => false) = true := by decide

/-! ## The fixture contract's law -/

theorem boolFlag_roundTrips : boolFlag.roundTrips [true] = true := by decide
theorem boolFlag_schemaAgrees : boolFlag.schemaAgrees ["ok"] = true := by decide +kernel
theorem boolFlag_schema_has_no_extra : boolFlag.schemaAgrees ["ok", "extra"] = false := by
  decide +kernel
theorem closedObjectFields_needs_closed :
    closedObjectFields (Json.mkObj [("type", Json.str "object")]) = none := by decide

theorem boolFlag_accepts_true :
    (match boolFlag.accept (encodeBoolFlag true) with
     | .ok true => true
     | _ => false) = true := by decide

theorem boolFlag_rejects_false :
    (match boolFlag.accept (encodeBoolFlag false) with
     | .error (.illFormed "bool" _) => true
     | _ => false) = true := by decide

theorem boolFlag_rejects_extra_key :
    (match boolFlag.accept (Json.mkObj [("ok", Json.bool true), ("extra", Json.bool true)]) with
     | .error (.unknownFields "bool" ["extra"]) => true
     | _ => false) = true := by decide

/-! ## The usage object is under the same rule as the rest of the header -/

theorem decodeUsage_accepts_counts :
    (match decodeUsage (Json.mkObj [("usage", Json.mkObj [("promptTokens", (12 : Json)),
        ("completionTokens", Json.null), ("totalTokens", (20 : Json))])]) with
     | .ok u => u.promptTokens == some 12 && u.completionTokens == none && u.totalTokens == some 20
     | .error _ => false) = true := by decide +kernel

theorem decodeUsage_absent_is_empty :
    (match decodeUsage (Json.mkObj [("tag", Json.str "header")]) with
     | .ok u => u.isEmpty
     | .error _ => false) = true := by decide +kernel

theorem decodeUsage_rejects_unknown_key :
    (match decodeUsage (Json.mkObj [("usage", Json.mkObj [("note", Json.str "edited")])]) with
     | .error (.unknownFields "header.usage" ["note"]) => true
     | _ => false) = true := by decide +kernel

theorem decodeUsage_rejects_non_object :
    (match decodeUsage (Json.mkObj [("usage", Json.str "hello")]) with
     | .error (.expectedObject "header.usage") => true
     | _ => false) = true := by decide +kernel

theorem decodeUsage_rejects_text_count :
    (match decodeUsage (Json.mkObj [("usage", Json.mkObj [("promptTokens", Json.str "12")])]) with
     | .error (.wrongType "header.usage" "promptTokens" _) => true
     | _ => false) = true := by decide +kernel

/-! ## Replay is tamper-evident for pure tools -/

theorem replay_echo_receipt :
    (match replay (receipt ollama (.invoke "c1" (.echo "hi"))) with
     | .ok "hi" => true
     | _ => false) = true := by decide +kernel

theorem replay_rejects_tampered_result :
    (match replay { receipt ollama (.invoke "c1" (.echo "hi")) with
        events := #[.invoke "c1" (.echo "hi"), .result "c1" "tampered", .finish "tampered"] } with
     | .error (.illFormed "transcript.result" "output does not match execute") => true
     | _ => false) = true := by decide +kernel

/-! ## The storage round trip, for every value

A transcript line written by the encoder and read back by the decoder is the value
it was, for every value, not only the fixtures above. The object maps involved have
fixed keys, so each decode reduces to its result by definitional unfolding alone,
whatever the strings and numbers inside: these proofs are `rfl`. The two decoders
that refuse a blank value are first stated with their condition, then discharged by
it. The text level, `Json.compress` then `Json.parse`, is Lean core's and is checked
on a fixture by `lake test`, not proved here. -/

theorem decodeTaggedDemoTool_encodeDemoTool (t : DemoTool) (h : nonemptyText t.payload = true) :
    decodeTaggedDemoTool (encodeDemoTool t) = .ok t := by
  cases t with
  | echo text =>
    have step : decodeTaggedDemoTool (encodeDemoTool (.echo text)) =
        if nonemptyText text then .ok (.echo text)
        else .error (.illFormed "tool.text" "blank") := rfl
    simp only [DemoTool.payload] at h
    simp [step, h]
  | arxivSearch query =>
    have step : decodeTaggedDemoTool (encodeDemoTool (.arxivSearch query)) =
        if nonemptyText query then .ok (.arxivSearch query)
        else .error (.illFormed "tool.query" "blank") := rfl
    simp only [DemoTool.payload] at h
    simp [step, h]

/-- Every event decodes to itself, given only what `Event.decodable` asks: that a
reasoning line and an invoked tool's payload are not blank. The call id, output,
detail, attempt and turn are arbitrary. -/
theorem decodeEvent_encodeEvent (e : Event DemoTool) (h : e.decodable = true) :
    decodeEvent (encodeEvent e) = .ok e := by
  cases e with
  | invoke callId tool =>
    have step : decodeEvent (encodeEvent (.invoke callId tool)) =
        (decodeTaggedDemoTool (encodeDemoTool tool)).bind fun t => .ok (.invoke callId t) := rfl
    simp only [Event.decodable] at h
    rw [step, decodeTaggedDemoTool_encodeDemoTool tool h]
    rfl
  | result callId output => rfl
  | repair attempt detail => rfl
  | reasoning turn content =>
    have step : decodeEvent (encodeEvent (.reasoning turn content)) =
        if nonemptyText content then .ok (.reasoning turn content)
        else .error (.illFormed "event" "blank reasoning") := rfl
    simp only [Event.decodable] at h
    simp [step, h]
  | finish content => rfl

/-- Every stop reason decodes to itself, whatever the attempt count. -/
theorem decodeStop_encodeStop (s : StopReason) : decodeStop (encodeStop s) = .ok s := by
  cases s <;> rfl

end LeanAgent
