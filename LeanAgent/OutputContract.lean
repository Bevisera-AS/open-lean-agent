module

public import Lean.Data.Json
public import LeanAgent.Json
public import LeanAgent.ToolSpec
public meta import LeanAgent.Json
public meta import LeanAgent.ToolSpec

namespace LeanAgent

open Lean

public section

/-- JSON on the wire, Lean on accept. The accept type is a parameter; this
module does not import LeanSpec.

The four parts are independent fields, so a contract's one law is checked, not
built in: `roundTrips` says that well-formed values survive `encode` then
`accept`, and `schemaAgrees` that the schema requires exactly the decoder's
fields and nothing else. `OutputContract.ofFields` builds both halves from one
field list, as the tool DSL builds a `ToolSpec`. -/
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

/-- The contract's law on representative values: each is well-formed and comes
back unchanged from `encode` then `accept`. Pair it with `#guard`. -/
public def OutputContract.roundTrips {α : Type} [BEq α] (c : OutputContract α)
    (samples : List α) : Bool :=
  !samples.isEmpty && samples.all fun a =>
    c.wellFormed a &&
      (match c.accept (c.encode a) with
       | .ok b => b == a
       | .error _ => false)

/-- The names an object schema marks `required`, when it is a closed object
(`additionalProperties: false`); `none` for any other schema. -/
public def closedObjectFields (schema : Json) : Option (List String) := do
  let closed ← (schema.getObjVal? "additionalProperties" >>= (·.getBool?)).toOption
  if closed then none
  let required ← (schema.getObjVal? "required" >>= (·.getArr?)).toOption
  let names ← required.toList.mapM fun j => j.getStr?.toOption
  let props ← (schema.getObjVal? "properties" >>= (·.getObj?)).toOption
  let declared := props.toList.map (·.1)
  if declared.all names.contains && names.all declared.contains then some names else none

/-- The schema is a closed object whose required fields are exactly `fields`,
the list the decoder's `exactFields` check uses. -/
public def OutputContract.schemaAgrees {α : Type} (c : OutputContract α) (fields : List String) :
    Bool :=
  match closedObjectFields c.schema with
  | some names => names.all fields.contains && fields.all names.contains
  | none => false

/-- A contract over a flat JSON object from one field list: the schema's
`properties`, `required` and `additionalProperties: false` come from `fields`,
and so does the `exactFields` check the decoder runs before `decodeFields`
reads the values. The schema cannot advertise a field the decoder refuses, nor
the reverse; `schemaAgrees` holds by construction. -/
public def OutputContract.ofFields {α : Type} (name : String) (fields : List (String × Json))
    (decodeFields : Json → Except DecodeError α) (encode : α → Json) (wellFormed : α → Bool) :
    OutputContract α := {
  name
  schema := objectParams (fields.map (·.1)).toArray fields
  decode := fun j => do
    let o ← asObj name j
    exactFields name (fields.map (·.1)) o
    decodeFields j
  encode
  wellFormed
  repairHint := defaultRepairHint name
}

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
public def boolFlag : OutputContract Bool :=
  OutputContract.ofFields "bool" [("ok", Json.mkObj [("type", Json.str "boolean")])]
    decodeBoolFlag encodeBoolFlag (fun b => b)

#guard boolFlag.roundTrips [true]
#guard boolFlag.schemaAgrees ["ok"]
#guard !boolFlag.schemaAgrees ["ok", "extra"]
#guard closedObjectFields (Json.mkObj [("type", Json.str "object")]) == none

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
