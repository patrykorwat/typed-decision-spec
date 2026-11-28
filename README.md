# typed-decision-spec

Machine-checked contract spec for **typed decision engines** — System 1
(single-pass, e.g. basal-2.0) and System 1.5 (looped, e.g. SanSi,
arXiv 2610.07730). Core Lean 4 only — no Mathlib, no external dependencies.

The pattern follows `radoskoppl/sejmbench` `docs/lean`: definitions in Lean,
golden vectors derived from the spec (never from an engine), sha256-pinned,
and a differential conformance suite. Scope is deliberately the **contract**:
typed answers, confidence gating, deferral, loop semantics. Accuracy and
calibration quality are empirical and stay in prose.

## What is proved (and where the claim comes from)

| Theorem | File | Contract claim |
|---|---|---|
| `Response` (structure) | `Basic.lean` | response is bound to the DECLARED options (`declared` is a field — a response pointing outside the caller's options is not constructible); K ≥ 2 enforced; `probs` is the integer core of `p ∈ Δ^K`: entries ≤ 100 and summing to 100 |
| `top_ge_100_over_K` | `Basic.lean` | normalization forces the top probability ≥ 100/K (pigeonhole) |
| `gate_conforming` | `Defer.lean` | the FULL gate contract: below the certified threshold the gate returns NO decision, and at or above it the gate DECIDES with the argmax payload — typed by `QType`, via the SHARED predicate `gateP` (one definition for gate, witness and export) |
| `selective_not_conforming` | `Defer.lean` | a gate that decides below threshold outside `act`/`tool` violates the contract — the REPORTED basal 2.8.1 finding as a type (one counterexample type kills the universal claim) |
| `isHard_K2` | `Defer.lean` | hard-answer boundary pinned (EVALUATION threshold, SanSi §4): for binary questions, hard answer iff confidence ≥ 75% |
| `runBin_length` / `budget_at` | `Loop.lean` | one run with T loops yields every budget 1..T (per SanSi §3; `h_0` is the token encoding, not a readout), and budget t's confidence sits at INDEX t-1 of the trace |
| `binConf_sound` | `Loop.lean` | **the trace and the Response contract are connected by construction**: every trace entry is the confidence of a CONSTRUCTED normalized binary response (`binResponseOf`) — a number impossible for the declared response shape cannot enter the trace |
| `reinjection_differs` | `Loop.lean` | re-injecting tokens each loop is a DIFFERENT model — demonstrated by a witness |
| `wrong_loop_never_decides` / `no_calib_never_decides` | `Loop.lean` | a calibration applies only at its own question type and loop index; without a calibration record the engine refuses |

`spec_T = 8` is pinned like sejmbench's `MIN_TRACK_RECORDS`: other budgets
are a `v2`, never a silent change. The exporter takes NO T parameter —
it reads `spec_T` — so a frozen budget cannot drift silently.

## Question-type scope (normative vs. deferred)

The current `Response` (single argmax over declared options, normalized
distribution) is normative for **`choice`** and — as of `TypedDecision/QTypes.lean`
— **`noul`** (the `BinaryResponse` witness: exactly two declared options;
`tieBinary` shows the no-decision boundary is a well-formed state) and
**`multi`** (the `MultiResponse` witness: **separate per-label binary
distributions with update locality** — `multi_set_independent` proves
the structural half; the statistical half is NOT claimed, since separate
marginals do not determine a joint distribution; labels are UNIQUE
(`labels_nodup`), `multiSet` indexes with `Fin` (no phantom labels), and
`gateMulti` returns a `MultiDecisionResult` that keeps the label–decision
mapping — proved length agreement, whole-collection deferral below the
threshold, and update locality). A multi question has **at least one
label** (`labels_nonempty`) — the empty collection is not a question,
and it keeps `Fin m.labels.length` inhabited.

**`score`** (as of v1.5, hardened v1.5.1, `TypedDecision/QTypes.lean`) —
a **scalar-value contract, deliberately NOT a `BinaryResponse` variant**:
`ScoreResponse` carries a `value` on the explicit [0, 100] scale
(`value_le_100`) plus a `confidence` in the Pct sense (`conf_le_100`)
**and the confidence's source loop** (`confidenceLoopIdx`) — separate
quantities, neither functionally determined by the other
(`value_differs_from_confidence`: 85 predicted with 55% certainty;
`same_conf_diff_value` — same confidence, different values;
`same_value_pair_differs` — same value, different confidences;
`same_conf_diff_loop` — different loops for the same confidence). The
**expected value** is defined EXACTLY (`exactEVnum`: Σ value·weight — the rational EV is
pinned by `expectedValue_floor` (100·EV ≤ Σ v·w ≤ 100·EV + 99) and
shown non-vacuous by `expectedValueTruncates` ([(0,50),(1,50)]: exact
1/2, integer 0); `scoreOfDist` builds the canonical response. Calibration
is a separate object (`ScoreCalib` — own τ, `threshold_le_100` as the
structural scale bound ONLY, and `loopIdx`); `gateScore` decides **with
the predicted value as payload** (`gateScore_payload_is_value`) and
abstains on a wrong loop (`gateScore_wrong_loop_never_decides`) and
below its own threshold (`gateScore_defers_below`). **Provenance
decision, recorded:** `confidenceLoopIdx` is *trusted adapter metadata*,
not a proof of origin (`loops_are_metadata` exhibits a response with
confidence 55 bound to loop 5 regardless of where the value came from);
full provenance would need a loop-indexed type — deliberately deferred.
**`gateScoreResult` is the public contract shape for gating results**
(`gateScoreResult_is_public_shape`): it carries BOTH loop indices —
the response's `confLoopIdx` AND the calibration's `calibLoopIdx` — so
the pairing travels with the decision and a mismatch becomes visible in
the value itself; plain `gateScore` stays the internal helper. Python
conformance: golden score from different loops, all gating branches
mirrored three-way (none / payload=value / wrong-loop, frozen == Lean ==
Python), per-label distributions compared, ill-formed responses (out of
scale in BOTH directions, non-integers including bool/float/str) rejected
by validation, EV=54 demo with exact numerator 5400.

For `act` and `tool` the semantics genuinely differ. **`act`** (as of
v1.6.3) is formalized as the **expected-cost contract with enforced
invariants**: `ActResponse` carries per-action cost distributions whose
entries are `CostEntry`s — each cost CARRIES its own scale proof
(`cost_le_max`, so an out-of-scale cost is unrepresentable at the entry
level; no separate caller obligation) — whose weights are normalized to
100 (`dists_normalized`), whose exact cost numerators EQUAL the
computed map (`nums_eq_map` — "computed, never supplied" holds for the
whole type), and whose `selected` is a minimum of the exact numerators
AND first-declared among minima (`sel_min` + `sel_first` over
`actions.idxOf` — a caller cannot silently select an expensive action,
and a tie cannot be resolved toward a later declaration). `ActCalib.τ`
is a **confidence threshold** (`threshold_le_100`, ≤ 100 — the gate
compares τ with `r.confidence`, never with a cost; MAX_COST is a
separate notion). `gateAct` decides with the action as payload and
abstains on wrong loop and below threshold. The tie-break is a PROVED
obligation, not prose: the export builds a tied response through
`actOfDists` (two actions with the same exact numerator 3000) and the
frozen tie vector crosses the whole Lean → frozen → Python bridge
(`act_tie_*`), with the Python golden test deriving the expected winner
independently (`nums.index(min(nums))` — the FIRST minimum). The
**public result shape mirrors score**: `gateActResult` carries the
decision AND both loop indices (`gateActResult_is_public_shape`), so
the conf-loop ↔ calib-loop pairing travels for act as well. The
selected index is guarded non-vacuous (`selected_idxOf_lt`). The
floor-lossy witness is normalized (`floor_loses_information`:
[(1,50),(1,50)] exact 100 vs [(3,50),(0,50)] exact 150 — same floor 1,
different numerators, weights summing to 100 on both sides). Every
exported act gate result is COMPUTED by `gateAct` over the constructed
response — no literal gate values. The Python mirror rejects negative
loop indices (mirror of `Nat` semantics).

**`tool`** (as of v1.7) is the **next-step contract**:
`ToolResponse` — the selected next step from a declared, non-empty,
duplicate-free vocabulary with a confidence (trustworthiness of the
choice itself, own loop) — `ToolCalib`/`gateTool` (payload = the
selected tool; abstains below τ and on wrong loop), `ToolDecisionResult`
(both loop indices travel; `gateToolResult_is_public_shape`),
`tool_selected_idxOf_lt` (non-vacuity). Deliberately NO cost model and
NO tie-break: the next-step choice carries no declared ordering
quantity (act is the cost-bearing sibling). At the contract level all
six question types are formalized, and all six are connected through
the typed `ResponseFor` family (below).

**`ResponseFor`** (as of v2.0 Phase A) is now in place: a dependent
family mapping each `QType` to ITS OWN contract structure
(`ResponseFor QType.act = ActResponse` etc. — all six dispatch
theorems are `rfl`), with a non-degeneracy witness per member
(`ResponseFor_inhabited`). The contracts keep their distinct
invariants by definition — this is a typed unification of the
assignment, NOT a flattening. The per-contract gates stay (their
payload and provenance types differ); the production adapter is a
separate later milestone (#16 Phase B).

## Proof audit (current as of v2.0-a)

All 199 top-level declarations of the library (`Basic`, `Defer`,
`Loop`, `QTypes`) were checked with `#print axioms`: every checked
dependency set is a subset of
`[propext, Quot.sound, Classical.choice]` — **no `sorryAx`, no new
axioms**. Zero `sorry`/`admit` in any module. Full `lake build` PASS;
full conformance suite (24 tests, INCLUDING the Lean export — no
`--fast`) passes with exit 0; both CI jobs green. Scope boundary: the
formal claims are the ones named in this README; conformance tests
mirror them in Python and are differential (frozen == Lean == Python).

## Recorded design decisions (external review round, 2026-11-27)

Findings from the external audit that were verified TRUE but
deliberately NOT changed (each re-derivable from the code):

* **`probs_le_100` is implied by `sum_100`** (every element of a `List
  Nat` is at most its sum) — kept as an explicit field: the mirrors
  validate bounds in BOTH directions independently, and review v1
  demanded the invariants as fields. Same for `declared_len_2` vs
  `declared_pair`.
* **`ActResponse.exactCostNums` could be a plain `def`** — true; the
  field form is the accepted design and both forms make wrong supply
  unrepresentable. Not changed (avoided breaking the reviewed API for
  zero guarantee gain).
* **`distCostSum`/`exactCostNum`/`expectedCost` parallel the score
  machinery** — deliberate: the contracts are separate by design; the
  shared abstraction is the `ResponseFor` target (#16).
* **`gateMulti` takes a raw τ, not a `Calib`** — deliberate: it is the
  evaluation-side pointwise lift; loop binding is the structural
  layer's job (`LoopResponse`/`Calib`).
* **`loopIdx` is unbounded metadata** — the recorded provenance
  decision; the index-typed variant is named in `binLoopResponse`'s
  docstring as the full-strength version.
* **`binLoopResponse` can mislabel `qtype`** (e.g. `noul` over
  `["a", "b"]`) — true Tier-1 laxity; the fix IS `ResponseFor` (#16).
* **The loop layer is binary-only (K = 2)** — now documented in the
  `Loop` module docstring; multi-class readouts are the #16 target.
* **`MultiDecisionResult` carries no label invariants** — consistent
  with `ScoreDecisionResult`: result types carry provenance, response
  types carry well-formedness.
* **`gate`/`selectiveGate` parameter order vs `Conforming`'s** —
  cosmetic; the one-line wrapper stays.
* **`max_sub_ge` kept** despite being derivable from
  `top_ge_100_over_K`: that derivation needs the same max-atom case
  analysis (verified against omega), so the dedicated helper is
  cheaper than the "general" route.

## Confidence semantics for evaluation data (act and tool)

**`act`** — the confidence of `ActResponse`, with its own loop
(`confidenceLoopIdx`), describes **the trustworthiness of the action
choice itself**: how much the model trusts that the selected action is
the right one. It is NOT the magnitude of a cost, and NOT the
certainty of a single cost forecast. Its measurable correctness
criterion lives in evaluation data, OUTSIDE this model (module
docstring, `QTypes.lean`); this README fixes the definition that any
collection and labeling protocol MUST use when judging act confidence:

* a labeled act item records the action that SHOULD have been chosen
  and whether the model's selection was correct — confidence is scored
  against **selection correctness**, never against the cost value and
  never against a per-forecast error;
* when scoring, use the confidence carried by the SAME response as the
  selection (the `confLoopIdx`/`calibLoopIdx` pairing of
  `gateActResult` — a mismatch means the score does not describe the
  gated decision).

**`tool`** — the same discipline, with the next-step-specific reading:
the confidence of `ToolResponse` measures the trustworthiness of the
NEXT-STEP CHOICE — whether the selected tool was the right next step
for the state and goal. It is scored against **selection correctness**,
and explicitly NOT against the technical success of the tool
invocation: a correctly chosen tool may still fail at runtime, and a
tool may execute cleanly although it should not have been used at all.
The same pairing requirement applies (`confLoopIdx`/`calibLoopIdx` of
`gateToolResult`).

The formal side (separate quantity, own loop, gate abstention) is
proved above and must not drift from the evaluation protocol's
wording. This is the definition referenced by issue #14 (act) before
closing, extended to tool with its own reading.

## Three thresholds, kept apart

1. **HardAnswerThreshold** (`isHard`) — evaluation-only (SanSi §4 metrics:
   an unanswerable item is right when the model gives no hard answer,
   top probability below (1+1/K)/2). NOT a production gating policy.
2. **CalibrationThreshold** (`Calib.τ`) — operational, question-type
   specific, from `basal-calibrate`. `certified : τ ≤ 100` is only the
   structural bound of the stored number; statistical certification is
   empirical and outside this model. The frozen pin carries the
   calibration threshold separately from the evaluation boundary.
3. **DecisionGate** (`gate`) — the policy consuming a calibration.

## The basal 2.8.1 max_error finding: reported, not independently certified

Observed on a live basal 2.8.1 server (2026-11, recorded in the
basal-serve workflow notes): `max_error` accepted in the payload with
zero deferrals below the certified threshold on `choice`/`noul`/`score`/
`multi`; only `act`/`tool` gated. NOTE: the published v2.8.1 API docs
describe `max_error` for choice/noul/score with an `abstain` result
field — that docs/behavior gap is itself part of the finding, and this
repository does not contain an independent HTTP reproduction.
Status: **reported finding, reproduction pending** (`selectiveGate` /
`UngatedEngine` encode the *class*, not the verified instance).

## Conformance bridge (three-way, with explicit boundary)

`test-vectors/tier1.json` carries Tier-1 golden vectors derived from the
spec's pinned integer math, frozen and sha256-checked (`vectors_sha256`,
canonical form with the field removed). `conformance/conformance.py` runs
a three-way differential test:

1. **Lean** — `conformance/ExportVectors.lean` computes the expected
   values FROM the proved definitions: `runBin` (not a re-derived map),
   `isHard` via its Decidable instance (not a duplicated formula), the
   shared `gateP`, and `spec_T` (no CLI T to drift). This closes the
   "generator implements its own math" gap for the definitions that are
   actually proved about.
2. **Frozen** — the sha256-pinned vectors.
3. **Python engines** — `ReferenceEngine` must match every vector;
   `ReinjectedEngine` (re-injects tokens) must DIVERGE and match its own
   frozen trace (executable twin of `reinjection_differs`);
   `SwappedReadoutEngine` (heads assigned to wrong loops) must DIVERGE
   (per-loop readout is testable); `UngatedEngine` must violate
   conformance below the calibration threshold for every affected
   question type while `act`/`tool` stay gated; a calibration fitted at
   loop 3 must not gate loop 8 even when its threshold would decide
   there (twin of `wrong_loop_never_decides`).

**Boundary of the three-way check** (stated, not hidden): it covers the
ITERATIVE part of the pipeline — trace, `isHard`, gate. `encode`
(sha256 → h0) exists only in Python and is asserted against the frozen
h0; the Lean export receives H0 precomputed, because sha256 is not in
Lean core. The hash stored next to the data detects accidental drift;
provenance is the git history of `gen_vectors.py` plus the Lean export
run recorded in CI logs.

```
lake build                                # the proofs (zero errors)
python3 conformance/conformance.py        # 24 tests incl. the Lean export, exit 0
python3 conformance/conformance.py --fast # skip the Lean export
```

## Scope — read before citing

* This is a spec artifact: it proves properties of the **specification**.
  The conformance bridge provides frozen Tier-1 vectors and differential
  testing for the pinned integer math. This is fixed-sample regression
  testing, **not** a machine-checked equivalence between the spec and any
  real engine (basal, SanSi or otherwise).
* Percentages are the integer core (`Pct = Nat`, bounded and normalized
  on `Response`); calibration files stay decimal. Extended contract
  surface (probabilities as exact distributions, `extract`, `multi`
  min/max, error costs) is Tier-2 and outside this revision.
* Settling behaviour of loops (SanSi §5.2: 89.1% of answers final by
  loop 4, fixes/breaks ~3:1 until loop 5) is EMPIRICAL — deliberately
  not a theorem.
* Refusal of quantized checkpoints without readable scales (the basal
  2.8.1 `-FP8` fix) is an engine invariant of the same refusal class as
  `no_calib_never_decides`; a first-class theorem needs a weights model
  and is Tier-2.

## Version history

* **v2.0-a** (2026-11-27, #16 Phase A): `ResponseFor : QType → Type` —
  the typed unification. A dependent family mapping each question type
  to ITS OWN contract structure (six `rfl` dispatch theorems — no
  weakening, no wrapper layer; the contracts keep their distinct
  invariants by definition), plus `ResponseFor_inhabited`
  (a non-degeneracy witness per member, each a contract's own demo
  object). Deliberately NO generic gate over the family for this phase
  (payload/provenance types differ across contracts — recorded); the
  production adapter is Phase B, a separate milestone. No export or
  frozen change (the bridge is untouched — the family adds no exported
  fields); suite 22/22, 199 declarations audited.
* **v1.7.2** (2026-11-27, review round 3): `act_actions` and
  `act_tie_actions` exported from the constructed responses (the
  single-source vocabulary rule now covers every exported list; values
  identical, pin unchanged); the issue-#14 reference moved under the
  act paragraph.
* **v1.7.1** (2026-11-27, re-review follow-ups): `tool_tools` exported
  FROM the constructed response (single vocabulary source);
  wrong-loop vectors through the whole bridge for BOTH act and tool
  (`act_gate_wrong_loop`, `tool_gate_wrong_loop` — calib at loop 5,
  the response's confidence from loop 2, computed by the gates,
  frozen, asserted in the bridge and the goldens); evaluation-section
  extended to tool (next-step correctness vs technical success of the
  invocation); `gate_conforming` claim-table row updated to the full
  contract (abstention below τ AND argmax payload at/above). New pin
  `3d13041d…`.
* **v1.7** (2026-11-27, #15): the **tool contract** — the last of the
  six question types at the contract level: `ToolResponse` (selection
  from a declared duplicate-free vocabulary + confidence with its own
  loop), `toolOf` (canonical constructor), `ToolCalib`/`gateTool`
  (payload = the selected tool; abstains below τ and on wrong loop),
  `ToolDecisionResult`/`gateToolResult` (both loop indices travel;
  public-shape theorem), `tool_selected_idxOf_lt` non-vacuity.
  Deliberately no cost model and no tie-break (recorded in the module
  docstring). Export: all 10 tool fields computed from the constructed
  responses through `gateTool` (below-τ, positive, τ = 100 boundary);
  frozen keys `tool_*` (new pin `7b9dd1c6…`); Python mirror with
  strict-int/negative-index validation; golden derives membership and
  distinctness from the exported lists.
* **v1.6.4** (2026-11-27, re-review follow-ups — #17): QTypes module
  docstring updated (act formalized, tool deferred, `Conforming`
  described as the base-`Response` gate contract); NON-trivial tie
  witness (`demoTie2Min`/`demoTie2First` — selection at index 1 with
  the earlier action strictly more expensive; `tie2_first_only` proves
  the later-tied selection's obligation unsatisfiable, hence
  unbuildable; `tie2Resp` shows the honest construction exists);
  `reinjection_conf_differs` — the divergence witnessed with BOTH
  engines' numbers through the same `binConfOf` transformation (98 vs
  99); stale build-test numbers fixed; confidence-semantics section for
  evaluation data added (the last #14 item).
* **v1.6.3** (2026-11-27, external review round — #17): `Conforming`
  strengthened to the full gate contract (safe deferral AND sound
  argmax decision — a never-deciding gate no longer qualifies);
  `reinjection_differs` re-proved over the ACTUAL engines with a valid
  `Readout` (`confAt` removed); the gateCalib/gateLoop theorem family
  completed (wrong type, below-τ, deciding path, `gateOptLoop`);
  `ActDecisionResult`/`gateActResult` added (mirror of
  `ScoreDecisionResult`); `Response.declared_nodup` enforced;
  `selected_idxOf_lt` non-vacuity guard; `score_gate_updated`
  serialized as number|null (consistent with the payload fields);
  scale-boundary vectors (τ = 100, conf = 100) through the whole
  bridge; dead `hsub` and unused `isHard_K2_pct` removed;
  `gateLoop_eq_gateCalib` proved by `rfl`. See also the recorded
  design decisions above.
* **v1.2** (this revision): P1-1 — trace confidences derived from
  CONSTRUCTED normalized binary responses (`binResponseOf`/`binConf`,
  `binConf_sound`); per-loop readout with a loop-index term and a
  swapped-heads detector; P1-2 — exporter calls `runBin`/`isHard`/
  `gateP`/`spec_T` directly (no duplicated formulas, no CLI T);
  P1-3 — real Python `isHard`/`gateP` mirrors vs. frozen vectors,
  encode boundary documented, calibration loop-binding test;
  P1-4 — per-loop readout tested; P2 — tautologies and duplicates
  removed, thresholds split (evaluation vs. calibration), argparse CLI,
  Lean subprocess error handling; QType scope section added
  (`ResponseFor` deferred to Tier-2).
* **v1.1** (2026-11-23): response bound to declared options; K ≥ 2 and
  normalization enforced (`probs ≤ 100`, `sum = 100`); `Conforming` typed
  by `QType`; calibration bound to its own type and loop index
  (`wrong_loop_never_decides`); loop trace budgets 1..T with per-loop
  readout (`read : Nat → Nat → Pct`); `budget_at` pins the exact index;
  hard-answer (eval) threshold separated from calibration threshold;
  basal 2.8.1 finding downgraded to reported + docs-contradiction note;
  conformance bridge extended with the Lean differential export.
* **v1.0** (2026-11-23): initial revision.

## Building

Requires [elan](https://github.com/leanprover/lean4); toolchain pinned in
`lean-toolchain` (currently `leanprover/lean4:v4.36.0`). Core Lean only:

```
lake build          # inside this directory
```

CI runs the same build in the `lean-spec` job of `.github/workflows/ci.yml`
and the three-way conformance suite in `conformance` (which builds the
project first, then runs the Lean export) — a proof or a vector that no
longer holds fails the build loudly instead of silently drifting.

## Files

* `TypedDecision.lean` — root module
* `TypedDecision/Basic.lean` — response contract (declared options, K ≥ 2, normalization)
* `TypedDecision/Defer.lean` — gating, deferral, threshold separation
* `TypedDecision/Loop.lean` — looped engines (System 1.5), calibration binding
* `test-vectors/tier1.json` — frozen Tier-1 vectors (sha256-pinned)
* `conformance/gen_vectors.py` — derives and freezes the vectors (run once)
* `conformance/ExportVectors.lean` — computes expected values from the Lean definitions
* `conformance/conformance.py` — three-way differential conformance suite
* `conformance/adapter.py` — Phase B reference adapter (issue #19):
  `build(q, engine_output)` keyed dispatch, `choice`/`noul` slice
* `.github/workflows/ci.yml` — `lean-spec` + `conformance` jobs
