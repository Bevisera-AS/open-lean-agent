module

public import Lean
public meta import Lean

/-!
`samples% T` is a list with one value per constructor of the closed inductive
`T`, every field filled with the string `"sample"`. It is the sample list
`ToolSet.covers` takes, generated from the inductive instead of kept by hand, so
a constructor added to a role's tool type is covered the moment it exists: if
no declaration projects it, the `covers` guard fails, and nothing can get out of
step with the inductive.

The fields of every tool constructor in this package are strings; a constructor
with a field of another type is an elaboration error that names it, and such a
catalog writes its sample list by hand.
-/

namespace LeanAgent

open Lean Elab Term Meta

public meta section

syntax (name := samplesStx) "samples% " ident : term

/-- The constructors of `T` with each explicit field a string literal, as a list
literal, elaborated against the expected type. -/
@[term_elab samplesStx]
def elabSamples : TermElab := fun stx expectedType? => do
  match stx with
  | `(samples% $T:ident) =>
    let tName ← realizeGlobalConstNoOverloadWithInfo T
    let .inductInfo info ← getConstInfo tName
      | throwErrorAt T "samples%: {tName} is not an inductive type"
    if info.numParams != 0 || info.numIndices != 0 then
      throwErrorAt T "samples%: {tName} has parameters or indices"
    let mut terms : Array Term := #[]
    for c in info.ctors do
      let .ctorInfo ci ← getConstInfo c
        | throwErrorAt T "samples%: {c} is not a constructor"
      let args ← forallTelescopeReducing ci.type fun xs _ => do
        xs.mapM fun x => do
          let ty ← whnf (← inferType x)
          if ty.isConstOf ``String then
            pure (Syntax.mkStrLit "sample" : Term)
          else
            throwErrorAt T "samples%: field {← x.fvarId!.getUserName} of {c} has type {ty}, not String; give covers an explicit sample list"
      terms := terms.push (← `($(mkCIdent c) $args*))
    let list ← `([$terms,*])
    elabTerm list expectedType?
  | _ => throwUnsupportedSyntax

end

end LeanAgent
