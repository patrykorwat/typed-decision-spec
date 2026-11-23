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
| `gate_conforming` | `Defer.lean` | below the certified threshold the gate returns NO decision — typed by `QType`, via the SHARED predicate `gateP` (one definition for gate, witness and export) |
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
distribution) is normative for **`choice`** and **`noul`**. For `score`,
`multi`, `act` and `tool` the semantics genuinely differ (expected value
on a scale; independent label probabilities where `sum = 100` is NOT the
right invariant; expected-cost actions; agent next-step). A typed
`ResponseFor : QType → Type` is planned; until then this contract makes
no claim about those four types' payload semantics (their deferral
semantics ARE covered by `Conforming` for every `QType`).

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
lake build                                # the proofs (10/10, zero warnings)
python3 conformance/conformance.py        # 10 checks, exit 0
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
* `.github/workflows/ci.yml` — `lean-spec` + `conformance` jobs
