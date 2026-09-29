module

public import Lean.Data.Json
public import LeanAgent.Json
public meta import LeanAgent.Json

namespace LeanAgent

open Lean

public section

/-- JSON on the wire, Lean on accept. The accept type is a parameter; this
module does not import LeanSpec. -/
public structure OutputContract (α : Type) where
  name : String
  schema : Json
  decode : Json → Except DecodeError α
  encode : α → Json
  wellFormed : α → Bool
  repairHint : DecodeError → String

public def defaultRepairHint (name : String) (err : DecodeError) : String :=
  "The previous JSON failed Lean accept:\n" ++ err.pretty ++
    s!"\nReturn a complete {name} JSON object. Do not omit required fields or add unknown keys."

public def OutputContract.accept {α : Type} (c : OutputContract α) (j : Json) :
    Except DecodeError α := do
  let a ← c.decode j
  if c.wellFormed a then pure a
  else .error (.illFormed c.name "not well-formed")

public def decodeBoolFlag (j : Json) : Except DecodeError Bool := do
  let context := "bool"
  let o ← asObj context j
  exactFields context ["ok"] o
  let v ← field context "ok" j
  match v.getBool? with
  | .ok b => pure b
  | .error _ => .error (.wrongType context "ok" "boolean")

public def encodeBoolFlag (b : Bool) : Json :=
  Json.mkObj [("ok", Json.bool b)]

/-- Fixture contract: `{"ok": true}` is the only well-formed value. Extra keys
fail closed. Used to prove repair-then-accept without a spec type. -/
public def boolFlag : OutputContract Bool := {
  name := "bool"
  schema := Json.mkObj [
    ("type", Json.str "object"),
    ("properties", Json.mkObj [("ok", Json.mkObj [("type", Json.str "boolean")])]),
    ("required", Json.arr #[Json.str "ok"]),
    ("additionalProperties", Json.bool false)
  ]
  decode := decodeBoolFlag
  encode := encodeBoolFlag
  wellFormed := fun b => b
  repairHint := defaultRepairHint "bool"
}

#guard
  match boolFlag.accept (encodeBoolFlag true) with
  | .ok true => true
  | _ => false

#guard
  match boolFlag.accept (encodeBoolFlag false) with
  | .error (.illFormed "bool" _) => true
  | _ => false

#guard
  match boolFlag.accept (Json.mkObj [("ok", Json.bool true), ("extra", Json.bool true)]) with
  | .error e =>
    (boolFlag.repairHint e).contains "extra" &&
      (match boolFlag.accept (encodeBoolFlag true) with
       | .ok true => true
       | _ => false)
  | .ok _ => false

end

end LeanAgent
