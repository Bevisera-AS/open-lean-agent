module

public import LeanAgent.Semantics.LTS

/-!
# Invariants and gates of a transition system

Two kinds of rule, each checked one step at a time and then proved for every run:

- **Invariant** (`TrInv`, `TrInvOn`): if every single step keeps a property, every
  run keeps it, so every state reachable from a good start is good. `TrInvOn`
  restricts this to the labels a run is allowed to use, which is how a frame rule
  is stated ("no message except `applied` changes the knowledge base").
- **Gate** (`EntersOnlyVia`): if the only steps into a set of states carry a key
  label, every run that ends in the set without starting there contains the key.
  "A proposal is accepted only through an `accept` step" is a gate.

## Source

`TrInv`, `MTrInv` and `mtrInv_of_trInv` are adapted from CSLib,
`Cslib.Foundations.Semantics.LTS.Basic` (Apache 2.0,
<https://github.com/leanprover/cslib>). `TrInvOn` and `EntersOnlyVia` are ours.
-/

namespace LeanAgent.Semantics

universe u v

@[expose] public section

namespace LTS

variable {State : Type u} {Label : Type v} (lts : LTS State Label)

/-- Every step keeps `p`. -/
def TrInv (p : State → Prop) : Prop :=
  ∀ s μ s', p s → lts.Tr s μ s' → p s'

/-- Every run keeps `p`. -/
def MTrInv (p : State → Prop) : Prop :=
  ∀ s μs s', p s → lts.MTr s μs s' → p s'

/-- Every step whose label satisfies `ok` keeps `p`. -/
def TrInvOn (ok : Label → Prop) (p : State → Prop) : Prop :=
  ∀ s μ s', ok μ → p s → lts.Tr s μ s' → p s'

/-- The only steps from outside `goal` into `goal` carry a `key` label. -/
def EntersOnlyVia (goal : State → Prop) (key : Label → Prop) : Prop :=
  ∀ s μ s', ¬ goal s → goal s' → lts.Tr s μ s' → key μ

variable {lts}

/-- A rule kept by every allowed step is kept by every run that uses only allowed labels. -/
theorem TrInvOn.mtr {ok : Label → Prop} {p : State → Prop} (h : lts.TrInvOn ok p)
    {s s' : State} {μs : List Label} (hrun : lts.MTr s μs s') :
    (∀ μ ∈ μs, ok μ) → p s → p s' := by
  induction hrun with
  | refl => intro _ hp; exact hp
  | stepL htr _ ih =>
    intro hall hp
    exact ih (fun μ hm => hall μ (List.mem_cons_of_mem _ hm))
      (h _ _ _ (hall _ (List.mem_cons_self ..)) hp htr)

theorem TrInv.toTrInvOn {p : State → Prop} (h : lts.TrInv p) :
    lts.TrInvOn (fun _ => True) p :=
  fun s μ s' _ hp htr => h s μ s' hp htr

/-- If every step keeps `p`, every run keeps `p` (CSLib: `mtrInv_of_trInv`). -/
theorem TrInv.mtrInv {p : State → Prop} (h : lts.TrInv p) : lts.MTrInv p :=
  fun _ _ _ hp hrun => h.toTrInvOn.mtr hrun (fun _ _ => trivial) hp

/-- A rule that holds at the start and is kept by every step holds in every reachable state. -/
theorem TrInv.canReach {p : State → Prop} (h : lts.TrInv p) {s s' : State}
    (hp : p s) (hr : lts.CanReach s s') : p s' :=
  let ⟨_, hrun⟩ := hr
  h.mtrInv _ _ _ hp hrun

/-- A gate holds for runs: a run that ends in `goal` without starting there
contains a `key` label. -/
theorem EntersOnlyVia.mtr {goal : State → Prop} {key : Label → Prop}
    (h : lts.EntersOnlyVia goal key) {s s' : State} {μs : List Label}
    (hrun : lts.MTr s μs s') : ¬ goal s → goal s' → ∃ μ ∈ μs, key μ := by
  induction hrun with
  | refl => intro hns hg; exact absurd hg hns
  | @stepL s1 μ s2 _ _ htr _ ih =>
    intro hns hg
    cases Classical.em (goal s2) with
    | inl hg2 => exact ⟨μ, List.mem_cons_self .., h s1 μ s2 hns hg2 htr⟩
    | inr hng2 =>
      obtain ⟨ν, hν, hk⟩ := ih hng2 hg
      exact ⟨ν, List.mem_cons_of_mem _ hν, hk⟩

end LTS

end

end LeanAgent.Semantics
