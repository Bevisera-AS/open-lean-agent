module

/-!
# Labelled transition systems

A labelled transition system (LTS) is a set of states and a relation saying which
labelled step leads from which state to which. An agent's lifecycle, an app's
message loop and a proposal's status rules are all instances: the labels are the
actions (`propose`, `accept`, a UI message) and the states what the actions change.

This file gives the shared shape and the facts that hold for every LTS: runs of
several steps (`MTr`), how runs split and join, and reachability. Rules about
which states a run may reach live in `LeanAgent.Semantics.Invariant`.

## Source

Adapted from CSLib, `Cslib.Foundations.Semantics.LTS.Basic` (Fabrizio Montesi and
contributors, Apache 2.0, <https://github.com/leanprover/cslib>), restated without
Mathlib for Lean 4.35. As in CSLib, `MTr` is built from the left (`stepL`), so a
run's label list is built the same way as the run. The textbook reference is
F. Montesi, *Introduction to Choreographies*, Cambridge University Press, 2023.
-/

namespace LeanAgent.Semantics

universe u v

@[expose] public section

/-- A labelled transition system: `Tr s μ s'` says label `μ` takes `s` to `s'`. -/
structure LTS (State : Type u) (Label : Type v) where
  /-- The transition relation. -/
  Tr : State → Label → State → Prop

namespace LTS

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- The LTS of a partial step function: `step s μ = none` means `μ` is refused in `s`.
This is the shape of a status table such as `canTransition`. -/
def ofPartial (step : State → Label → Option State) : LTS State Label where
  Tr s μ s' := step s μ = some s'

/-- A state is terminal if no label leads anywhere from it. -/
def IsTerminal (s : State) : Prop :=
  ∀ μ s', ¬ lts.Tr s μ s'

/-- A run: `MTr s μs s'` says the labels `μs`, in order, take `s` to `s'`. -/
inductive MTr : State → List Label → State → Prop where
  | refl {s : State} : MTr s [] s
  | stepL {s1 : State} {μ : Label} {s2 : State} {μs : List Label} {s3 : State} :
      lts.Tr s1 μ s2 → MTr s2 μs s3 → MTr s1 (μ :: μs) s3

variable {lts}

/-- A run with no labels stays where it started. -/
theorem MTr.nil_eq {s1 s2 : State} (h : lts.MTr s1 [] s2) : s1 = s2 := by
  cases h
  rfl

theorem MTr.nil_iff {s1 s2 : State} : lts.MTr s1 [] s2 ↔ s1 = s2 :=
  ⟨MTr.nil_eq, fun h => h ▸ MTr.refl⟩

/-- One step is a run of length one. -/
theorem MTr.single {s1 s2 : State} {μ : Label} (h : lts.Tr s1 μ s2) : lts.MTr s1 [μ] s2 :=
  .stepL h .refl

/-- A run of length one is one step. -/
theorem MTr.single_invert {s1 s2 : State} {μ : Label} (h : lts.MTr s1 [μ] s2) :
    lts.Tr s1 μ s2 := by
  cases h with
  | stepL htr hrest => exact (MTr.nil_eq hrest) ▸ htr

theorem MTr.single_iff {s1 s2 : State} {μ : Label} : lts.MTr s1 [μ] s2 ↔ lts.Tr s1 μ s2 :=
  ⟨MTr.single_invert, MTr.single⟩

/-- Two runs, one after the other, are one run. -/
theorem MTr.comp {s1 s2 s3 : State} {μs1 μs2 : List Label}
    (h1 : lts.MTr s1 μs1 s2) (h2 : lts.MTr s2 μs2 s3) : lts.MTr s1 (μs1 ++ μs2) s3 := by
  induction h1 with
  | refl => exact h2
  | stepL htr _ ih => exact .stepL htr (ih h2)

/-- A run can be extended by one step at the end. -/
theorem MTr.stepR {s1 s2 s3 : State} {μs : List Label} {μ : Label}
    (h1 : lts.MTr s1 μs s2) (h2 : lts.Tr s2 μ s3) : lts.MTr s1 (μs ++ [μ]) s3 :=
  MTr.comp h1 (MTr.single h2)

/-- A run splits at any point of its label list. -/
theorem MTr.split {μs1 μs2 : List Label} :
    ∀ {s1 s3 : State}, lts.MTr s1 (μs1 ++ μs2) s3 →
      ∃ s2, lts.MTr s1 μs1 s2 ∧ lts.MTr s2 μs2 s3 := by
  induction μs1 with
  | nil => intro s1 _ h; exact ⟨s1, .refl, h⟩
  | cons μ μs ih =>
    intro s1 s3 h
    simp only [List.cons_append] at h
    cases h with
    | stepL htr hrest =>
      obtain ⟨s2, h1, h2⟩ := ih hrest
      exact ⟨s2, .stepL htr h1, h2⟩

/-- Splitting and joining: a run over `μs1 ++ μs2` is a run over `μs1` then one over `μs2`. -/
theorem MTr.append_iff {s1 s3 : State} {μs1 μs2 : List Label} :
    lts.MTr s1 (μs1 ++ μs2) s3 ↔ ∃ s2, lts.MTr s1 μs1 s2 ∧ lts.MTr s2 μs2 s3 :=
  ⟨MTr.split, fun ⟨_, h1, h2⟩ => MTr.comp h1 h2⟩

variable (lts) in
/-- `s2` can be reached from `s1` by some run. -/
def CanReach (s1 s2 : State) : Prop :=
  ∃ μs, lts.MTr s1 μs s2

theorem CanReach.refl (s : State) : lts.CanReach s s :=
  ⟨[], .refl⟩

theorem CanReach.of_tr {s1 s2 : State} {μ : Label} (h : lts.Tr s1 μ s2) : lts.CanReach s1 s2 :=
  ⟨[μ], MTr.single h⟩

theorem CanReach.trans {s1 s2 s3 : State} :
    lts.CanReach s1 s2 → lts.CanReach s2 s3 → lts.CanReach s1 s3
  | ⟨_, h1⟩, ⟨_, h2⟩ => ⟨_, MTr.comp h1 h2⟩

variable (lts) in
/-- `μs` is a trace of `s`: some run from `s` carries exactly these labels. -/
def IsTrace (s : State) (μs : List Label) : Prop :=
  ∃ s', lts.MTr s μs s'

/-- A prefix of a trace is a trace. -/
theorem IsTrace.of_append {s : State} {μs1 μs2 : List Label}
    (h : lts.IsTrace s (μs1 ++ μs2)) : lts.IsTrace s μs1 :=
  let ⟨_, hr⟩ := h
  let ⟨s2, h1, _⟩ := MTr.split hr
  ⟨s2, h1⟩

/-- In the LTS of a partial step, a state where every label is refused is terminal. -/
theorem ofPartial_isTerminal {step : State → Label → Option State} {s : State}
    (h : ∀ μ, step s μ = none) : (ofPartial step).IsTerminal s := by
  intro μ s' htr
  have : step s μ = some s' := htr
  rw [h μ] at this
  cases this

end LTS

end

end LeanAgent.Semantics
