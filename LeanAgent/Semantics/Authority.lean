module

public import LeanAgent.Semantics.Invariant

/-!
# Agent authority over transition systems

Rules about what an agent may do, stated once for any system whose steps record
who took them. A label is `Acted Actor Act`: the actor and what they did. The
caller says which actors are human (`isHuman`); everything else is an agent or
a system.

- **Agents only propose** (`AgentStepsLandIn`): every step an agent takes lands
  in an allowed set (for a knowledge base, `proposed`). Then a run made only of
  agent steps ends where it started or in the allowed set
  (`AgentStepsLandIn.mtr`), and if a goal such as `accepted` is outside the
  allowed set, every run that reaches the goal contains a human step
  (`AgentStepsLandIn.humanGate`, `humanStep_of_reach`).
- **Agents never do** (`AgentNeverDoes`): some acts (send, export, widen
  visibility) are never taken by an agent. Then no agent-only run contains one
  (`AgentNeverDoes.mtr`).
- **Budget** (`Budgeted`): every step uses up fuel. Then no run is longer than the
  fuel it started with (`Budgeted.length_le`), which is how a bounded agent loop
  is stated.

The rules say nothing about who the humans are or how many: the propose, review
and accept rights may all be held by one person.

## Source

Ours, on top of the CSLib-derived `LTS` in this package. `Budgeted` is the
ranking-function form of CSLib's `Cslib.Foundations.Relation.Termination`.
-/

namespace LeanAgent.Semantics

universe u v w

@[expose] public section

/-- A step label recording who took the step and what they did. -/
structure Acted (Actor : Type v) (Act : Type w) where
  actor : Actor
  act : Act

namespace LTS

/-- No step in `μs` is taken by a human. -/
def NoHumanStep {Actor : Type v} {Act : Type w} (isHuman : Actor → Prop)
    (μs : List (Acted Actor Act)) : Prop :=
  ∀ l ∈ μs, ¬ isHuman l.actor

section Authority

variable {State : Type u} {Actor : Type v} {Act : Type w}
  (lts : LTS State (Acted Actor Act))

/-- Every step a non-human takes lands in `agentMay`. -/
def AgentStepsLandIn (isHuman : Actor → Prop) (agentMay : State → Prop) : Prop :=
  ∀ s l s', ¬ isHuman l.actor → lts.Tr s l s' → agentMay s'

/-- No non-human step carries a `forbidden` act. -/
def AgentNeverDoes (isHuman : Actor → Prop) (forbidden : Act → Prop) : Prop :=
  ∀ s l s', ¬ isHuman l.actor → forbidden l.act → ¬ lts.Tr s l s'

variable {lts} {isHuman : Actor → Prop}

/-- A run of agent steps only ends where it started or in `agentMay`. -/
theorem AgentStepsLandIn.mtr {agentMay : State → Prop}
    (h : lts.AgentStepsLandIn isHuman agentMay) {s s' : State}
    {μs : List (Acted Actor Act)} (hrun : lts.MTr s μs s') :
    NoHumanStep isHuman μs → s' = s ∨ agentMay s' := by
  induction hrun with
  | refl => intro _; exact .inl rfl
  | @stepL s1 l s2 _ _ htr _ ih =>
    intro hn
    cases ih (fun l' hl' => hn l' (List.mem_cons_of_mem _ hl')) with
    | inl heq => exact .inr (heq ▸ h s1 l s2 (hn l (List.mem_cons_self ..)) htr)
    | inr hm => exact .inr hm

/-- If agents only land in `agentMay` and `goal` lies outside it, only a human
step enters `goal`. -/
theorem AgentStepsLandIn.humanGate {agentMay goal : State → Prop}
    (h : lts.AgentStepsLandIn isHuman agentMay) (hdisj : ∀ s, agentMay s → ¬ goal s) :
    lts.EntersOnlyVia goal (fun l => isHuman l.actor) := by
  intro s l s' _ hg htr
  exact Classical.byContradiction fun hnh => hdisj s' (h s l s' hnh htr) hg

/-- Every run that reaches `goal` from outside it contains a human step. -/
theorem AgentStepsLandIn.humanStep_of_reach {agentMay goal : State → Prop}
    (h : lts.AgentStepsLandIn isHuman agentMay) (hdisj : ∀ s, agentMay s → ¬ goal s)
    {s s' : State} {μs : List (Acted Actor Act)} (hrun : lts.MTr s μs s')
    (hs : ¬ goal s) (hs' : goal s') : ∃ l ∈ μs, isHuman l.actor :=
  (h.humanGate hdisj).mtr hrun hs hs'

/-- A run of agent steps only never enters `goal` from outside it. -/
theorem AgentStepsLandIn.agentRun_avoids {agentMay goal : State → Prop}
    (h : lts.AgentStepsLandIn isHuman agentMay) (hdisj : ∀ s, agentMay s → ¬ goal s)
    {s s' : State} {μs : List (Acted Actor Act)} (hrun : lts.MTr s μs s')
    (hn : NoHumanStep isHuman μs) (hs : ¬ goal s) : ¬ goal s' := by
  intro hg
  obtain ⟨l, hl, hh⟩ := h.humanStep_of_reach hdisj hrun hs hg
  exact hn l hl hh

/-- A run of agent steps only contains no forbidden act. -/
theorem AgentNeverDoes.mtr {forbidden : Act → Prop}
    (h : lts.AgentNeverDoes isHuman forbidden) {s s' : State}
    {μs : List (Acted Actor Act)} (hrun : lts.MTr s μs s') :
    NoHumanStep isHuman μs → ∀ l ∈ μs, ¬ forbidden l.act := by
  induction hrun with
  | refl => intro _ l hl; cases hl
  | @stepL s1 l s2 _ _ htr _ ih =>
    intro hn l' hl'
    cases hl' with
    | head => exact fun hf => h s1 l s2 (hn l (List.mem_cons_self ..)) hf htr
    | tail _ hm => exact ih (fun l'' hl'' => hn l'' (List.mem_cons_of_mem _ hl'')) l' hm

end Authority

section Budget

variable {State : Type u} {Label : Type v} {lts : LTS State Label}

variable (lts) in
/-- Every step strictly lowers `fuel`. -/
def Budgeted (fuel : State → Nat) : Prop :=
  ∀ s μ s', lts.Tr s μ s' → fuel s' < fuel s

/-- Along a run, the steps taken plus the fuel left never exceed the fuel at the start. -/
theorem Budgeted.mtr {fuel : State → Nat} (h : lts.Budgeted fuel) {s s' : State}
    {μs : List Label} (hrun : lts.MTr s μs s') : μs.length + fuel s' ≤ fuel s := by
  induction hrun with
  | refl => simp
  | @stepL s1 μ s2 _ _ htr _ ih =>
    have := h s1 μ s2 htr
    simp only [List.length_cons]
    omega

/-- No run is longer than the fuel it starts with. -/
theorem Budgeted.length_le {fuel : State → Nat} (h : lts.Budgeted fuel) {s s' : State}
    {μs : List Label} (hrun : lts.MTr s μs s') : μs.length ≤ fuel s :=
  Nat.le_trans (Nat.le_add_right _ _) (h.mtr hrun)

end Budget

end LTS

end

end LeanAgent.Semantics
