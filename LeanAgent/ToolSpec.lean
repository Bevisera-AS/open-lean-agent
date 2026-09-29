module

public import Lean.Data.Json

namespace LeanAgent

open Lean

public section

/-- Wire tool schema. Independent of any closed call inductive. -/
public structure ToolSpec where
  name : String
  description : String
  parameters : Json

public def objectParams (required : Array String) (properties : List (String × Json)) : Json :=
  Json.mkObj [
    ("type", Json.str "object"),
    ("properties", Json.mkObj properties),
    ("required", Json.arr (required.map Json.str)),
    ("additionalProperties", Json.bool false)
  ]

public def encodeToolSpec (t : ToolSpec) : Json :=
  Json.mkObj [
    ("type", Json.str "function"),
    ("function", Json.mkObj [
      ("name", Json.str t.name),
      ("description", Json.str t.description),
      ("parameters", t.parameters)
    ])
  ]

end

end LeanAgent
