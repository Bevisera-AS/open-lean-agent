module

public import Lean.Data.Json
public import LeanAgent.Util
public import LeanAgent.Json
public import LeanAgent.ToolSpec
public import LeanAgent.ToolSet
public meta import LeanAgent.Json
public meta import LeanAgent.ToolSpec
public meta import LeanAgent.ToolSet

/-!
A value-level DSL for the common case: tools whose arguments are a fixed set of
non-blank string fields (query, path, content, code, …). The caller still owns
the closed `Tool` inductive — that is what carries the safety guarantee — but
`mkToolSet` generates the repetitive `decode`/`decodeTagged`/`encodeTagged`/
`name`/`argumentsJson`/`specs` plumbing uniformly and fail-closed, so a new tool
is a few lines instead of ~7 near-identical definitions.
-/

namespace LeanAgent

open Lean

public section

/-- One tool, described as an ordered list of required string fields plus the
maps to/from the caller's closed `Tool` type.

* `build vals` receives the field values in `fields` order and returns the tool
  (it only fails if the caller's own invariant beyond non-blankness fails; the
  DSL already guarantees each value is present and non-blank).
* `project t` returns the field values iff `t` is *this* constructor, else
  `none`; that is how encoding/naming dispatch back to the right declaration. -/
public structure ToolDecl (Tool : Type) where
  name : String
  description : String
  fields : List String
  build : List String → Except DecodeError Tool
  project : Tool → Option (List String)
  /-- This tool's effect on the store (read / propose / commit). Defaults to `read`. -/
  effect : ToolEffect := .read

/-- Property JSON for a string field. -/
private def strProp (field : String) : String × Json :=
  (field, Json.mkObj [("type", Json.str "string")])

public def ToolDecl.spec {Tool : Type} (d : ToolDecl Tool) : ToolSpec := {
  name := d.name
  description := d.description
  parameters := objectParams d.fields.toArray (d.fields.map strProp)
}

/-- Read each declared field as a non-blank string, in order, from `args`.
`ctx` is the error context (e.g. `tool.read_file`); `extra` names any keys that
are allowed in addition to the fields (used to allow the `tag` key when decoding
the tagged transcript form). -/
private def readFields (ctx : String) (fields : List String) (extra : List String)
    (args : Json) : Except DecodeError (List String) := do
  let o ← asObj ctx args
  exactFields ctx (extra ++ fields) o
  fields.mapM fun f => do
    let v ← strField ctx f args
    if nonemptyText v then pure v
    else .error (.illFormed s!"{ctx}.{f}" "blank")

/-- Find the declaration matching a wire tool name. -/
private def declByName {Tool : Type} (decls : List (ToolDecl Tool)) (name : String) :
    Option (ToolDecl Tool) :=
  decls.find? (·.name == name)

/-- Build a `ToolSet` from a closed list of `ToolDecl`s. Off-catalog names/tags
are rejected with `invalidTag`, unknown fields with `unknownFields`, and blank
values with `illFormed` — the same fail-closed behavior as a hand-written set.

`execute?` defaults to observation-only (`fun _ => none`); pass a real projection
for tools that can be replayed purely (like `echo`). -/
public def mkToolSet {Tool : Type} (decls : List (ToolDecl Tool))
    (execute? : Tool → Option String := fun _ => none)
    (isCite : Tool → Bool := fun _ => false)
    (usableCite : String → Bool := fun s => nonemptyText s) : ToolSet Tool :=
  -- The first declaration whose `project` matches, with its extracted values.
  -- Every reachable tool must be covered by some declaration.
  let matchDecl (t : Tool) : Option (ToolDecl Tool × List String) :=
    match decls.find? (fun d => (d.project t).isSome) with
    | some d => some (d, (d.project t).getD [])
    | none => none
  {
    specs := (decls.map ToolDecl.spec).toArray
    execute?, isCite, usableCite
    effect := fun t =>
      match matchDecl t with | some (d, _) => d.effect | none => .read
    name := fun t =>
      match matchDecl t with | some (d, _) => d.name | none => ""
    argumentsJson := fun t =>
      match matchDecl t with
      | some (d, vals) => Json.mkObj (List.zip d.fields (vals.map Json.str))
      | none => Json.mkObj []
    encodeTagged := fun t =>
      match matchDecl t with
      | some (d, vals) => Json.mkObj (("tag", Json.str d.name) :: List.zip d.fields (vals.map Json.str))
      | none => Json.mkObj [("tag", Json.str "")]
    decode := fun name args =>
      match declByName decls name with
      | none => .error (.invalidTag "tool" "name" name)
      | some d => do d.build (← readFields s!"tool.{d.name}" d.fields [] args)
    decodeTagged := fun j => do
      let tag ← strField "tool" "tag" j
      match declByName decls tag with
      | none => .error (.invalidTag "tool" "tag" tag)
      | some d => do d.build (← readFields "tool" d.fields ["tag"] j)
  }

/-! ## Convenience constructors for the most common shapes -/

/-- A tool with a single required string field. -/
public def toolDecl1 {Tool : Type} (name description field : String)
    (mk : String → Tool) (get : Tool → Option String) : ToolDecl Tool := {
  name, description, fields := [field]
  build := fun vals => match vals with
    | [v] => .ok (mk v)
    | _ => .error (.illFormed s!"tool.{name}" "arity")
  project := fun t => (get t).map (fun v => [v])
}

/-- A tool with two required string fields. -/
public def toolDecl2 {Tool : Type} (name description f1 f2 : String)
    (mk : String → String → Tool) (get : Tool → Option (String × String)) : ToolDecl Tool := {
  name, description, fields := [f1, f2]
  build := fun vals => match vals with
    | [a, b] => .ok (mk a b)
    | _ => .error (.illFormed s!"tool.{name}" "arity")
  project := fun t => (get t).map (fun (a, b) => [a, b])
}

/-! ## Tests: a two-tool demo set exercising the generated machinery. -/

private inductive Demo where
  | one (q : String)
  | two (p c : String)
  deriving Repr, BEq

private def demoSet : ToolSet Demo := mkToolSet [
  toolDecl1 "search" "one field" "query" Demo.one
    (fun | .one q => some q | _ => none),
  toolDecl2 "put" "two fields" "path" "content" Demo.two
    (fun | .two p c => some (p, c) | _ => none)
]

#guard (demoSet.specs.map (·.name)).toList == ["search", "put"]

-- decode by name
#guard
  match demoSet.decode "search" (Json.mkObj [("query", Json.str "hi")]) with
  | .ok (.one "hi") => true
  | _ => false

-- off-catalog name refuses
#guard
  match demoSet.decode "shell" (Json.mkObj [("cmd", Json.str "rm")]) with
  | .error (.invalidTag "tool" "name" "shell") => true
  | _ => false

-- unknown field fails closed
#guard
  match demoSet.decode "search" (Json.mkObj [("query", Json.str "hi"), ("x", Json.str "y")]) with
  | .error (.unknownFields "tool.search" ["x"]) => true
  | _ => false

-- blank value rejected
#guard
  match demoSet.decode "search" (Json.mkObj [("query", Json.str "  ")]) with
  | .error (.illFormed "tool.search.query" "blank") => true
  | _ => false

-- two-field decode + argumentsJson + tagged round-trip
#guard
  match demoSet.decode "put" (Json.mkObj [("path", Json.str "a"), ("content", Json.str "b")]) with
  | .ok t =>
    demoSet.name t == "put" &&
      Json.compress (demoSet.argumentsJson t) == "{\"content\":\"b\",\"path\":\"a\"}" &&
      (match demoSet.decodeTagged (demoSet.encodeTagged t) with
       | .ok t2 => t2 == t
       | .error _ => false)
  | _ => false

-- tagged decode rejects an off-catalog tag
#guard
  match demoSet.decodeTagged (Json.mkObj [("tag", Json.str "nope"), ("query", Json.str "x")]) with
  | .error (.invalidTag "tool" "tag" "nope") => true
  | _ => false

end

end LeanAgent
