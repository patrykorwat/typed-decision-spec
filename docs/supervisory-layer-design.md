# Supervisory layer design note: nondeterministic decisions before code (#25)

Status: **design (spike, A1)** — no Lean or adapter code in this commit. This
note records the design of a supervisory layer over the existing contracts
BEFORE any code, mirroring the #18 spike precedent. Implementation
sub-issues #26 (A2), #27 (A3), #28 (A4) are confirmed or re-scoped by this
note; adjustments are recorded here, not silently.

## Problem

The current contracts answer one question: *is this response conformant?*
— a gate over ONE response against declared options, thresholds and loop
provenance (`gateP`, `gateLoop`, `gateScore`, `gateAct`, `gateTool`,
`gateMulti`). They do not answer the supervisory question: *can any
behavior of the model and the environment, within the declared model,
violate the system's rules?* — over sequences of proposals and their
outcomes. That question does not need probabilities on model behavior; it
needs a nondeterministic transition RELATION (a set of possible successors,
no weights) plus an invariant the system must never leave. This layer is
that relation and its safety theorems. Empirical model quality (accuracy,
ECE, settling) stays outside, as everywhere in this repo.

## Prior art (checked 2026-11; positions, do not re-derive)

* **LeanGuard** (arXiv:2611.02332): Lean 4 policies checked at runtime over
  tool calls, fail-closed, with the decision procedure proved against an
  independent temporal semantics. Closest neighbor — but it consumes RAW
  tool calls. Our layer consumes typed, gate-checked responses WITH loop
  provenance: the provenance problem LeanGuard solves at the string level
  is already closed structurally upstream (`ResponseFor`, `LoopResponse`,
  `confidenceLoopIdx`); our layer inherits that, and this is the recorded
  positioning claim.
* **Soteria** (arXiv:2611.17880), **Agent-C**, **VEPA**, **ToolGate**:
  runtime enforcement / verified planning; none formalize a
  confidence-calibration contract layer beneath the enforcement.
* **MDPLib** (Lean): probabilistic MDPs — the P2 direction (#31), explicitly
  OUT of scope here.

## Recorded decisions

### D1. Shape — `DecisionSystem` (adopted, with a core-only amendment)

```
structure DecisionSystem where
  State       : Type
  Action      : Type
  Observation : Type
  proposals   : State → List Observation
  interpret   : State → Observation → Option Action
  admissible  : State → Action → Prop
  transition  : State → Action → List State
  invariant   : State → Prop
```

`SafeAction D s a := admissible s a ∧ ∀ s' ∈ transition s a, invariant s'`.

**Amendment (written rationale):** the issue sketch uses `Finset`. `Finset`
is NOT in Lean core (Mathlib-only) and this repo is core-only, zero
dependencies — so the carrier is `List` with the collection discipline
already used throughout the spec: `nodup` and non-emptiness become
obligations on the structure (the mirror of `labels_nodup` /
`labels_nonempty` / tool-vocabulary constraints), not per-call hypotheses
re-established at every use. Duplicates in a transition set would double
count successors in quantified statements; a non-deterministic relation
with an empty successor set for an ADMITTED action is vacuous (see D4).

### D2. Input discipline — the layer sits BEHIND the adapter (adopted)

The supervisory layer consumes responses that already passed the Phase B
path: a proposal is a typed `(q : QType) × ResponseFor q` object with its
loop index readable FROM THE STRUCTURE (`LoopResponse.loopIdx`,
`confidenceLoopIdx`), never re-derived from a side argument. The layer
must NOT recreate the provenance problem that `confidenceLoopIdx` closed:
it never receives a raw engine string, and it never receives an index as
an untyped field. Concretely: the concrete `Observation`/proposal carrier
of an instantiation is the adapter's `build(q, engine_output)` output (or
its Lean twin, the canonical constructors) — the supervisor observes
gate-checked responses, and its `interpret` maps such an observation to an
action (`Option`: an observation need not license any action).

### D3. `Response.probs` is NEVER a transition kernel (adopted — standing boundary)

`probs` is a PREDICTION distribution over declared answer options,
normalized to 100. A transition kernel weights successor states of the
SYSTEM. Conflating the two is a methodological error: the same numbers
would then do double duty as "what the model will say" and "what the world
will do", which is exactly the statistical-independence confusion the
multi contract refused to make ("separate distributions", marginals do not
determine the joint). This is a standing boundary: no theorem, mirror, or
export in the supervisory layer may take `probs` as weights over
`transition` successors. Probability assignments over transitions are the
P2/MDP spike (#31), out of scope.

### D4. Non-vacuity obligations (adopted — witnesses at construction)

Mirror of the `selected_idxOf_lt` / `tie2Resp` discipline: wherever the
spec admits an object, the object carries its own witness; a quantified
claim is never accepted over a possibly-empty domain. Concretely:

* **Relation nonempty**: for every `a` the layer ADMITS (`admissible s a`
  holds and the layer takes it), `transition s a` is nonempty — an
  admitted action with no modeled outcomes is not admissible; carried as a
  structure-level obligation on the instantiation, like `sel_min` on
  `ActResponse`.
* **Outcome coverage**: modeled outcomes cover at least `{success,
  failure}` — an invariant quantified over successors that can never fail
  proves nothing; the instantiation must present both (structural zero
  cells, if any, are proved separately, not assumed away).
* **Rejection witness**: at least one witness of a REJECTED proposal
  exists — the supervisor refuses something (`interpret` returning `none`,
  or an inadmissible action in the domain). A layer that never refuses is
  a pass-through, and its safety theorem would be about a different,
  trivial system.

Each of these is a construction-time field or a named lemma with a concrete
witness (`by decide` over the demo vocabulary pattern), not prose.

### D5. Location — a NEW module subtree (adopted)

`TypedDecision/Supervise/…` (e.g. `Supervise/Domain.lean` first, then
`Safety.lean`, then `Exec.lean` per the slice plan). `Basic.lean`,
`Defer.lean`, `Loop.lean`, `QTypes.lean` are UNTOUCHED — the
parallel-edit rule (new proof layers in separate modules) stands, and the
root module gains only `import` lines. No existing frozen vector changes;
new frozen keys, if any slice needs them, go through the canonical
regeneration procedure (one regeneration per round).

### D6. Out of scope (adopted)

Probability assignments over transitions; expected-cost optimization over
successors (the act contract's exact-cost discipline is about a SINGLE
decision's declared cost distribution, not about transition weights);
MDP/Bellman machinery (P2 spike, #31); runtime execution against real
engines (A4 models bounded execution as a relation over the declared
`DecisionSystem` — no wall-clock, no I/O). The supervisory layer adds
safety statements about the DECLARED model; it does not claim the model
matches the world — that gap stays empirical, like accuracy and ECE.

## Slice plan (sub-issues confirmed)

* **#26 (A2) — `DecisionSystem` domain module**: CONFIRMED, with the D1
  amendment (List carriers + nodup/nonempty obligations) and the D4
  non-vacuity witnesses as construction-time fields. Non-vacuity guards
  per the recorded discipline: the relation is inhabited, success and
  failure outcomes are both representable, a rejection witness exists.
* **#27 (A3) — safety theorems**: CONFIRMED. `safe_actions_only` (every
  action the layer takes is a `SafeAction`), `all_successors_safe`
  (invariance: stepping through a safe action from an invariant state
  lands in an invariant state — the induction step of the safety argument),
  `defer_on_uncertainty` (when the underlying gate abstains — below τ,
  wrong loop, no calibration, the `no_decide`/`gateLoop_defers` family —
  the supervisor's only admissible move is defer/hold: the gate's
  abstention PROPAGATES to the action layer instead of being silently
  repaired). The bridge from gate abstention to `admissible` is the
  theorem that makes D2 more than a convention.
* **#28 (A4) — bounded multi-step execution and failure recovery**:
  CONFIRMED with a scope note. Execution is bounded by a pinned `Nat`
  budget (the `spec_T` pattern: the bound is read from a definition, the
  exporter takes no parameter); failure recovery means the transition
  relation contains recovery paths from failure states (a D4 outcome-
  coverage consequence made constructive) and that bounded execution
  preserves the invariant — NOT runtime recovery of real engines. The
  multi-step trace mirrors the loop discipline: per-step state, no
  re-injection of untyped data between steps.

## Risks / open questions

* **Vacuous instantiation**: a `DecisionSystem` whose `invariant` holds
  everywhere, or whose `transition` is empty, proves safety trivially. The
  D4 witnesses are the guard, but the A2 slice must also include the
  NEGATIVE demonstration (a malformed system is unrepresentable or
  rejected), mirroring `selective_not_conforming`.
* **Quantifier shape over successors**: with a `List` carrier, statements
  quantify over membership (`∀ s' ∈ transition s a, …`); the pitfalls for
  `List.getElem?`-style statements and `l[i]!` side conditions apply —
  prefer membership forms in theorem statements (skill: lean-core-pitfalls).
* **Bridge scope**: A3's `defer_on_uncertainty` needs the gate's abstention
  observable at the supervisor's type level. The minimal bridge is: the
  supervisor sees the gate's `Option`-shaped decision result (payload or
  `none`) as the observation; richer provenance threading is its own
  design question if attempted — this note deliberately does not
  generalize the loop layer beyond K = 2 (the Phase B §5 note stands).
* **Not an MDP**: no rewards, no discounting, no Bellman equations. If P2
  (#31) later wants probabilities, it extends `transition` to a weighted
  form as a SEPARATE structure — this layer's theorems must remain true of
  the unweighted one (a weighted kernel is a refinement, never a
  prerequisite).
