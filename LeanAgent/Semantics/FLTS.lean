module

public import LeanAgent.Semantics.Invariant

/-!
# Functional labelled transition systems

A functional LTS (FLTS) has exactly one next state for each state and label: a step
function `tr : State → Label → State`. An Elm-style app is one, with
`tr s m := (update m s).1`, and so is any message loop that never refuses a message.
A run is then a left fold of the step function over the labels.

This file proves that the fold and the relational view (`toLTS`) agree, so every
result about LTS runs applies to an FLTS, and gives the frame rule `Preserves`:
if no allowed label changes a view of the state, no run of allowed labels does.

## Source

`FLTS`, `mtr` and its fold lemmas are adapted from CSLib,
`Cslib.Foundations.Semantics.FLTS.Basic` and `FLTSToLTS` (Apache 2.0,
<https://github.com/leanprover/cslib>). `Preserves` is ours.
-/

namespace LeanAgent.Semantics

universe u v w

@[expose] public section

/-- A functional LTS: label `μ` takes state `s` to `tr s μ`. -/
structure FLTS (State : Type u) (Label : Type v) where
  /-- The step function. -/
  tr : State → Label → State

namespace FLTS

variable {State : Type u} {Label : Type v} (flts : FLTS State Label)

/-- The state a run of labels `μs` ends in, from `s`. -/
def mtr (s : State) (μs : List Label) : State :=
  μs.foldl flts.tr s

/-- The relational view: `s` steps to `s'` under `μ` exactly when `tr s μ = s'`. -/
def toLTS : LTS State Label where
  Tr s μ s' := flts.tr s μ = s'

/-- A view of the state that no allowed label changes. -/
def Preserves {β : Sort w} (ok : Label → Prop) (view : State → β) : Prop :=
  ∀ s μ, ok μ → view (flts.tr s μ) = view s

variable {flts}

theorem mtr_nil {s : State} : flts.mtr s [] = s := rfl

theorem mtr_cons {s : State} {μ : Label} {μs : List Label} :
    flts.mtr s (μ :: μs) = flts.mtr (flts.tr s μ) μs := rfl

theorem mtr_append {s : State} {μs1 μs2 : List Label} :
    flts.mtr s (μs1 ++ μs2) = flts.mtr (flts.mtr s μs1) μs2 :=
  List.foldl_append

theorem mtr_concat {s : State} {μs : List Label} {μ : Label} :
    flts.mtr s (μs ++ [μ]) = flts.tr (flts.mtr s μs) μ := by
  rw [mtr_append]; rfl

/-- The fold and the relational view agree: there is a run from `s` over `μs` to
`s'` exactly when folding `μs` from `s` gives `s'`. -/
theorem toLTS_mtr_iff {μs : List Label} :
    ∀ {s s' : State}, flts.toLTS.MTr s μs s' ↔ flts.mtr s μs = s' := by
  induction μs with
  | nil => intro s s'; exact LTS.MTr.nil_iff
  | cons μ μs ih =>
    intro s s'
    constructor
    · intro h
      cases h with
      | stepL htr hrest =>
        have htr' : flts.tr s μ = _ := htr
        subst htr'
        exact ih.mp hrest
    · intro h
      exact .stepL (rfl : flts.tr s μ = flts.tr s μ) (ih.mpr h)

/-- Every FLTS run is a run of its relational view. -/
theorem toLTS_mtr (s : State) (μs : List Label) : flts.toLTS.MTr s μs (flts.mtr s μs) :=
  toLTS_mtr_iff.mpr rfl

/-- The frame rule: a view no allowed label changes is unchanged by every run of
allowed labels. -/
theorem Preserves.mtr {β : Sort w} {ok : Label → Prop} {view : State → β}
    (h : flts.Preserves ok view) :
    ∀ (μs : List Label) (s : State), (∀ μ ∈ μs, ok μ) → view (flts.mtr s μs) = view s := by
  intro μs
  induction μs with
  | nil => intro s _; rfl
  | cons μ μs ih =>
    intro s hall
    rw [mtr_cons, ih _ (fun ν hν => hall ν (List.mem_cons_of_mem _ hν)),
      h s μ (hall μ (List.mem_cons_self ..))]

/-- An invariant of the step function holds after every run. -/
theorem trInv_mtr {p : State → Prop} (h : ∀ s μ, p s → p (flts.tr s μ))
    (s : State) (μs : List Label) (hp : p s) : p (flts.mtr s μs) :=
  (LTS.TrInv.mtrInv (lts := flts.toLTS) (fun s μ _ hp htr => htr ▸ h s μ hp))
    s μs _ hp (toLTS_mtr s μs)

end FLTS

end

end LeanAgent.Semantics
