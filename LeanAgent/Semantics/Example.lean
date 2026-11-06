module

public import LeanAgent.Semantics.FLTS
public import LeanAgent.Semantics.Authority
public meta import LeanAgent.Semantics.FLTS

/-!
# Worked example: a proposal lifecycle

A proposal starts as a `draft`, is `proposed`, and is then `accepted` or
`withdrawn`. The status table is a partial step function, so the lifecycle is
`LTS.ofPartial lifecycleStep`. The example shows the three rule shapes of this
library on one small system:

- a **gate**: a proposal becomes `accepted` only through an `accept` step, so
  every run from `draft` to `accepted` contains `accept`;
- a **terminal state**: nothing leaves `accepted`;
- an **invariant**: once `accepted`, every later state is `accepted`.

`sloppy` is the same table with one row wrong (`propose` jumps straight to
`accepted`). `sloppy_fails` proves the gate rejects it, so the gate is not
vacuously true.

The last section runs the same lifecycle as an FLTS, where a refused label leaves
the state unchanged, the way an app ignores a message it cannot apply.
-/

namespace LeanAgent.Semantics.Example

@[expose] public section

inductive Status where
  | draft
  | proposed
  | accepted
  | withdrawn
  deriving DecidableEq, Repr

inductive Act where
  | propose
  | accept
  | withdraw
  deriving DecidableEq, Repr

/-- The status table: `none` means the action is refused in that status. -/
def lifecycleStep : Status → Act → Option Status
  | .draft, .propose => some .proposed
  | .proposed, .accept => some .accepted
  | .proposed, .withdraw => some .withdrawn
  | _, _ => none

def lifecycle : LTS Status Act := LTS.ofPartial lifecycleStep

/-- Gate: the only step into `accepted` is `accept`. -/
theorem lifecycle_acceptedOnlyViaAccept :
    lifecycle.EntersOnlyVia (· = .accepted) (· = .accept) := by
  intro s μ s' hns hg htr
  subst hg
  cases s <;> cases μ <;> simp_all [lifecycle, LTS.ofPartial, lifecycleStep]

/-- Every run from `draft` that ends `accepted` contains an `accept` step. -/
theorem lifecycle_run_to_accepted_has_accept {μs : List Act}
    (h : lifecycle.MTr .draft μs .accepted) : Act.accept ∈ μs := by
  obtain ⟨μ, hμ, hk⟩ := lifecycle_acceptedOnlyViaAccept.mtr h (by decide) rfl
  exact hk ▸ hμ

/-- Nothing leaves `accepted`. -/
theorem lifecycle_accepted_terminal : lifecycle.IsTerminal .accepted :=
  LTS.ofPartial_isTerminal (fun μ => by cases μ <;> rfl)

/-- Invariant: once accepted, always accepted. -/
theorem lifecycle_accepted_stays : lifecycle.TrInv (· = .accepted) := by
  intro s μ s' hs htr
  subst hs
  exact absurd htr (lifecycle_accepted_terminal μ s')

/-- The same table with one wrong row: `propose` jumps straight to `accepted`. -/
def sloppyStep : Status → Act → Option Status
  | .draft, .propose => some .accepted
  | s, μ => lifecycleStep s μ

def sloppy : LTS Status Act := LTS.ofPartial sloppyStep

/-- The gate rejects the wrong table. -/
theorem sloppy_fails : ¬ sloppy.EntersOnlyVia (· = .accepted) (· = .accept) := by
  intro h
  have := h .draft .propose .accepted (by decide) rfl rfl
  cases this

/-! ## The lifecycle as an FLTS: a refused action changes nothing -/

def lifecycleApp : FLTS Status Act where
  tr s μ := (lifecycleStep s μ).getD s

/-- Frame rule: `withdraw` never moves a proposal into or out of `accepted`. -/
theorem lifecycleApp_withdraw_preserves_accepted :
    lifecycleApp.Preserves (· = .withdraw) (· == Status.accepted) := by
  intro s μ hμ
  subst hμ
  cases s <;> rfl

/-- Any number of `withdraw` steps leave "is accepted" unchanged. -/
theorem lifecycleApp_withdraws_keep_accepted (s : Status) (μs : List Act)
    (h : ∀ μ ∈ μs, μ = .withdraw) :
    (lifecycleApp.mtr s μs == .accepted) = (s == .accepted) :=
  lifecycleApp_withdraw_preserves_accepted.mtr μs s h

/-! ## Who takes the step: agents only propose -/

inductive Who where
  | human
  | agent
  deriving DecidableEq, Repr

/-- The lifecycle with actors: an agent may `propose` and `withdraw`; only a human
may `accept`. -/
def governed : LTS Status (Acted Who Act) where
  Tr s l s' := lifecycleStep s l.act = some s' ∧ (l.act = .accept → l.actor = .human)

/-- Every agent step lands in `proposed` or `withdrawn`. -/
theorem governed_agentStepsLandIn :
    governed.AgentStepsLandIn (· = .human) (fun s => s = .proposed ∨ s = .withdrawn) := by
  intro s l s' hnh ⟨hstep, hacc⟩
  rcases l with ⟨who, act⟩
  cases s <;> cases act <;> simp_all [lifecycleStep]

/-- Every run that ends `accepted` from below contains a human step. -/
theorem governed_accept_needs_human {s : Status} {μs : List (Acted Who Act)}
    (hrun : governed.MTr s μs .accepted) (hs : s ≠ .accepted) :
    ∃ l ∈ μs, l.actor = .human :=
  governed_agentStepsLandIn.humanStep_of_reach (goal := (· = .accepted))
    (fun s h => by rcases h with h | h <;> subst h <;> decide) hrun hs rfl

/-- An agent never takes `accept`. -/
theorem governed_agentNeverAccepts : governed.AgentNeverDoes (· = .human) (· = .accept) :=
  fun _ _ _ hnh hacc ⟨_, h⟩ => hnh (h hacc)

/-- The same table with the actor check removed. -/
def ungoverned : LTS Status (Acted Who Act) where
  Tr s l s' := lifecycleStep s l.act = some s'

/-- Without the actor check an agent can accept. -/
theorem ungoverned_fails :
    ¬ ungoverned.AgentNeverDoes (· = .human) (· = .accept) := by
  intro h
  exact h .proposed ⟨.agent, .accept⟩ .accepted (by decide) rfl rfl

/-! ## Budget: every step lowers a counter -/

/-- A loop with a fixed number of turns left: each step uses one. -/
def turns : LTS Nat Unit where
  Tr n _ n' := n = n' + 1

theorem turns_budgeted : turns.Budgeted id := fun s _ s' h => by
  have h' : s = s' + 1 := h
  simp only [id]; omega

/-- From `n` turns left no run is longer than `n`. -/
theorem turns_bounded {n m : Nat} {μs : List Unit} (h : turns.MTr n μs m) : μs.length ≤ n :=
  turns_budgeted.length_le h

/-! ## Tests -/

#guard lifecycleStep .draft .propose = some .proposed
#guard lifecycleStep .draft .accept = none
#guard lifecycleStep .accepted .withdraw = none
#guard sloppyStep .draft .propose = some .accepted
#guard lifecycleApp.mtr .draft [.propose, .accept] = .accepted
#guard lifecycleApp.mtr .draft [.accept, .propose] = .proposed
#guard lifecycleApp.mtr .draft [.propose, .withdraw, .accept] = .withdrawn
#guard lifecycleApp.mtr .accepted [.withdraw, .withdraw] = .accepted

end

end LeanAgent.Semantics.Example
