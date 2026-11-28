/-!
# Supervisory layer, part 1 (A2): the decision domain

Implements the #26 slice of the supervisory-layer design note
(docs/supervisory-layer-design.md, decisions D1/D4/D5). The layer answers
a DIFFERENT question than the response gates: not "is this response
conformant?", but "can any behavior of the model and environment, within
the declared model, violate the system's rules?" — over a NONDETERMINISTIC
transition RELATION (a set of possible successors, no weights, no
probabilities on model behavior).

Standing boundaries recorded in the design note and honored here:

* D2 — the layer sits BEHIND the Phase B path: a proposal is a typed,
  gate-checked observation; `interpret` maps it to an action or refuses
  (`Option`). The layer never re-derives loop provenance.
* D3 — `Response.probs` is a PREDICTION distribution over declared answer
  options, NEVER a transition kernel: no definition, theorem, export or
  mirror in this module may weight transition successors by `probs`.
  Probability over transitions is the P2/MDP spike (#31), out of scope.
* D1 amendment — the carrier is `List` (core-only, no Mathlib `Finset`):
  `Nodup` and non-emptiness are construction-time obligations on the
  structure (the mirror of `labels_nodup` / `labels_nonempty`), not
  per-call hypotheses. An admitted action with an empty successor set is
  VACUOUS and unrepresentable (D4).

The demo system (a deploy pipeline) carries its non-vacuity witnesses as
NAMED lemmas with concrete terms, never prose: a failure outcome and a
success outcome are both reachable, a proposal is REFUSED, an action is
INADMISSIBLE, and admissible does not imply safe (deploy from `ready` may
land in `failed`, which violates the invariant — that gap is exactly what
`SafeAction` closes and what the A3 theorems (#27) will quantify over).
-/

namespace TypedDecision

/-- A nondeterministic decision system: states, admissible actions, a
transition RELATION (`transition` returns the set of possible successors —
no probabilities), an invariant the system must never leave, and the
observation/action interface the supervisor consumes. The four proof
fields are the D1/D4 non-vacuity obligations carried at construction:
duplicate observations or successors would double-count members in
quantified statements, an empty proposal list is not a question, and an
ADMITTED action with no modeled outcome proves nothing. -/
structure DecisionSystem where
  State : Type
  Action : Type
  Observation : Type
  proposals : State → List Observation
  interpret : State → Observation → Option Action
  admissible : State → Action → Prop
  transition : State → Action → List State
  invariant : State → Prop
  proposals_nonempty : ∀ s, proposals s ≠ []
  proposals_nodup : ∀ s, proposals s |>.Nodup
  transition_nodup : ∀ s a, transition s a |>.Nodup
  admitted_transition_nonempty : ∀ s a, admissible s a → transition s a ≠ []

/-- A safe action: admissible AND every modeled successor preserves the
invariant. Admissibility alone does NOT imply safety — the demo system
below carries a concrete witness of the gap (`demo_deploy_not_safe_ready`). -/
def SafeAction (D : DecisionSystem) (s : D.State) (a : D.Action) : Prop :=
  D.admissible s a ∧ ∀ s' ∈ D.transition s a, D.invariant s'

/-! ## The demo system: a bounded deploy pipeline -/

/-- Demo states: `ready` → `deploying` → `live`, plus the failure state
`failed` (excluded by the invariant — the modeled failure outcome). -/
inductive SysState
  | ready | deploying | live | failed
  deriving DecidableEq, Repr

/-- Demo actions. -/
inductive SysAction
  | hold | deploy | rollback
  deriving DecidableEq, Repr

/-- Demo observations (proposals). `oJunk` is never interpretable — the
rejection witness; `oDeploy` outside `ready` and `oRollback` outside
`live`/`failed` are refused too. -/
inductive SysObs
  | oHold | oDeploy | oRollback | oJunk
  deriving DecidableEq, Repr

/-- Bool mirror of admissibility (export and decidability read the Bool;
`demoAdmissible` is the Prop the structure consumes). -/
def demoAdmissibleB : SysState → SysAction → Bool
  | _, SysAction.hold => true
  | SysState.ready, SysAction.deploy => true
  | SysState.failed, SysAction.rollback => true
  | SysState.live, SysAction.rollback => true
  | _, _ => false

/-- Admissibility as a predicate (Bool-backed: decidable by
construction, so the demo obligations and the conformance export share
one definition). -/
def demoAdmissible (s : SysState) (a : SysAction) : Prop :=
  demoAdmissibleB s a = true

/-- Bool mirror of the invariant: every state but `failed` is allowed. -/
def demoInvariantB : SysState → Bool
  | SysState.failed => false
  | _ => true

/-- The invariant: the system must never BE in the failure state
(reaching it is modeled — the nondeterministic deploy outcome — staying
in it is the violation the layer rules out). -/
def demoInvariant (s : SysState) : Prop :=
  demoInvariantB s = true

/-- Demo proposal vocabulary: the same four observations at every state
(the `interpret`/`admissible` pair does the state-dependent work). -/
def demoProposals : SysState → List SysObs
  | _ => [SysObs.oHold, SysObs.oDeploy, SysObs.oRollback, SysObs.oJunk]

/-- Demo interpretation: hold everywhere, deploy licensed only in
`ready`, rollback licensed only in `live`/`failed`, junk never. -/
def demoInterpret : SysState → SysObs → Option SysAction
  | _, SysObs.oHold => some SysAction.hold
  | SysState.ready, SysObs.oDeploy => some SysAction.deploy
  | SysState.failed, SysObs.oRollback => some SysAction.rollback
  | SysState.live, SysObs.oRollback => some SysAction.rollback
  | _, _ => none

/-- Demo transition RELATION: deploy may succeed or fail
(`ready`/`deploying` → two successors — the modeled outcome coverage);
hold loops in place; rollback recovers `live`/`failed` → `ready`. Empty
sets appear only for INADMISSIBLE combinations (the D4 obligation makes
an empty set for an admitted action unrepresentable). -/
def demoTransition : SysState → SysAction → List SysState
  | SysState.ready, SysAction.deploy => [SysState.deploying, SysState.failed]
  | SysState.ready, SysAction.hold => [SysState.ready]
  | SysState.deploying, SysAction.deploy => [SysState.live, SysState.failed]
  | SysState.deploying, SysAction.hold => [SysState.deploying]
  | SysState.live, SysAction.hold => [SysState.live]
  | SysState.live, SysAction.rollback => [SysState.ready]
  | SysState.failed, SysAction.hold => [SysState.failed]
  | SysState.failed, SysAction.rollback => [SysState.ready]
  | _, _ => []

/-! ### Standalone proofs of the demo obligations (structure fields
reference these — proofs inside a structure literal that must look at
OTHER fields of the same literal do not compose; the named-lemma route
is the repo pattern). -/

theorem demo_proposals_nonempty : ∀ s, demoProposals s ≠ [] :=
  fun _ => by simp [demoProposals]

theorem demo_proposals_nodup : ∀ s, demoProposals s |>.Nodup := by
  intro s; cases s <;> decide

theorem demo_transition_nodup : ∀ s a, demoTransition s a |>.Nodup := by
  intro s a
  cases s <;> cases a <;> simp [demoTransition] <;> decide

theorem demo_admitted_transition_nonempty :
    ∀ s a, demoAdmissible s a → demoTransition s a ≠ [] := by
  intro s a h
  cases s <;> cases a <;>
    simp [demoAdmissible, demoAdmissibleB, demoTransition] at h ⊢

/-! ### The constructed demo system

The obligations are the named lemmas above, supplied at construction: a
malformed demo (an admitted action with no modeled outcome, duplicate
successors or observations, an empty proposal list) is UNREPRESENTABLE —
the negative demonstration the design note requires, on the same pattern
as `sel_min` on `ActResponse`. -/

/-- The demo `DecisionSystem` (deploy pipeline). `abbrev` (reducible):
the projections (`demoSystem.State` etc.) must reduce to the demo
vocabulary at elaboration time, so witnesses and `simp` can see through
them — the `abbrev Pct` pattern. -/
abbrev demoSystem : DecisionSystem where
  State := SysState
  Action := SysAction
  Observation := SysObs
  proposals := demoProposals
  interpret := demoInterpret
  admissible := demoAdmissible
  transition := demoTransition
  invariant := demoInvariant
  proposals_nonempty := demo_proposals_nonempty
  proposals_nodup := demo_proposals_nodup
  transition_nodup := demo_transition_nodup
  admitted_transition_nonempty := demo_admitted_transition_nonempty

/-! ### Single-source bridges

The conformance export reads the CONSTRUCTED system's projections; these
`rfl`-bridges pin that the projections and the standalone demo functions
are the same terms (trace and export cannot diverge). -/

theorem demoSystem_transition (s : SysState) (a : SysAction) :
    demoSystem.transition s a = demoTransition s a := rfl

theorem demoSystem_interpret (s : SysState) (o : SysObs) :
    demoSystem.interpret s o = demoInterpret s o := rfl

theorem demoSystem_proposals (s : SysState) :
    demoSystem.proposals s = demoProposals s := rfl

theorem demoSystem_invariantB (s : SysState) :
    demoInvariantB s = true ↔ demoSystem.invariant s := Iff.rfl

/-! ### Non-vacuity witnesses (named lemmas, concrete terms) -/

/-- A FAILURE outcome is modeled and reachable: deploy from `ready` may
land in `failed`, which violates the invariant. -/
theorem demo_failure_outcome_reachable :
    ∃ s a s', s' ∈ demoSystem.transition s a ∧ ¬demoSystem.invariant s' :=
  ⟨SysState.ready, SysAction.deploy, SysState.failed,
    by simp [demoTransition], by simp [demoInvariant, demoInvariantB]⟩

/-- A SUCCESS outcome is modeled and reachable, to a DIFFERENT invariant
state (the relation is not a vacuous self-loop). -/
theorem demo_success_outcome_reachable :
    ∃ s a s', s' ∈ demoSystem.transition s a ∧ demoSystem.invariant s' ∧ s' ≠ s :=
  ⟨SysState.ready, SysAction.deploy, SysState.deploying,
    by simp [demoTransition], by simp [demoInvariant, demoInvariantB],
    by decide⟩

/-- REJECTION witness: the supervisor refuses an observation that is in
the proposal vocabulary but licenses no action. -/
theorem demo_rejection_witness :
    ∃ s o, o ∈ demoSystem.proposals s ∧ demoSystem.interpret s o = none :=
  ⟨SysState.ready, SysObs.oJunk,
    by simp [demoProposals], rfl⟩

/-- REFUSAL witness: a vocabulary action is INADMISSIBLE in a state
(`rollback` from `ready` — nothing to roll back). -/
theorem demo_rollback_not_admissible_ready :
    ¬demoSystem.admissible SysState.ready SysAction.rollback := by
  simp [demoAdmissible, demoAdmissibleB]

/-- Deploy IS admissible from `ready` — the next lemma shows it is not
SAFE: admissible and safe are deliberately different predicates. -/
theorem demo_deploy_admissible_ready :
    demoSystem.admissible SysState.ready SysAction.deploy := rfl

/-- The negative demonstration (mirror of `selective_not_conforming`):
an ADMISSIBLE action that is NOT a `SafeAction` — its modeled successor
set contains the failure state. Admissibility alone proves nothing about
the invariant; this gap is exactly what `SafeAction` closes. -/
theorem demo_deploy_not_safe_ready :
    ¬SafeAction demoSystem SysState.ready SysAction.deploy := by
  intro h
  rcases h with ⟨_, hin⟩
  have h9 := hin SysState.failed (by simp [demoTransition])
  simp [demoInvariant, demoInvariantB] at h9

/-- Hold is safe in EVERY invariant state (self-loop preserves the
invariant) — the demo's always-available safe move; `admissible` holds
for hold unconditionally, and the single successor is the state itself. -/
theorem demo_hold_safe_invariant :
    ∀ s, demoSystem.invariant s → SafeAction demoSystem s SysAction.hold := by
  intro s hs
  refine ⟨rfl, ?_⟩
  intro s' hs'
  have hstep : demoSystem.transition s SysAction.hold = [s] := by
    cases s <;> rfl
  rw [hstep] at hs'
  rcases List.mem_singleton.mp hs' with rfl
  exact hs

/-- The layer is not a vacuous pass-through of unsafety: a safe action
EXISTS (in an invariant state, hold). -/
theorem demo_safe_action_exists :
    ∃ s a, SafeAction demoSystem s a :=
  ⟨SysState.ready, SysAction.hold, demo_hold_safe_invariant SysState.ready rfl⟩

end TypedDecision
