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
| `Response` (structure) | `Basic.lean` | `conf` is the top probability; `argmax` indexes a declared option — "the answer can never fall outside the options you gave" (basal README; SanSi §3: `p ∈ Δ^K`, no text) |
| `gate_conforming` | `Defer.lean` | below the certified threshold the gate returns NO decision — for every question type |
| `ungated_not_conforming` | `Defer.lean` | a gate that decides below threshold outside `act`/`tool` violates the contract — the verified basal 2.8.1 finding (`max_error` accepted and silently ignored on `choice`/`noul`/`score`/`multi`) as a type |
| `isHard_K2` / `isHard_K2_pct` | `Defer.lean` | hard-answer boundary pinned: for binary questions, hard answer iff confidence ≥ 75% (SanSi §4 metrics: top probability below (1+1/K)/2) |
| `run_length` / `budget_at` | `Loop.lean` | one run with T loops stores every budget's readout — "one pass with T loops yields the decisions of all budgets 1..T" (SanSi §3) |
| `reinjection_differs` | `Loop.lean` | re-injecting tokens each loop is a DIFFERENT model — demonstrated by a witness (0 vs 1 at loop 1) |
| `no_calib_never_decides` | `Loop.lean` | a threshold without its loop index decides nothing — calibration is bound to the loop it was fitted at (SanSi §5.3: ECE best at loop 3, climbing again by loop 8) |

`spec_T = 8` is pinned like sejmbench's `MIN_TRACK_RECORDS`: other budgets
are a `v2`, never a silent change.

## Scope — read before citing

* This is a spec artifact: it proves properties of the **specification**.
  The conformance bridge below provides frozen Tier-1 vectors and
  differential testing for the pinned integer math. This is fixed-sample
  regression testing, **not** a machine-checked equivalence between the
  spec and any real engine (basal, SanSi or otherwise).
* Percentages are the integer core (`Pct = Nat`, 0..100): the contract is
  pinned on integers, calibration files stay decimal. Extended contract
  surface (probabilities as exact distributions, `extract`, `multi`
  min/max, error costs) is Tier-2 and outside this revision.
* Settling behaviour of loops (SanSi §5.2: 89.1% of answers final by
  loop 4, fixes/breaks ~3:1 until loop 5) is EMPIRICAL — deliberately
  not a theorem.
* Refusal of quantized checkpoints without readable scales (the basal
  2.8.1 `-FP8` fix) is an engine invariant of the same refusal class as
  `no_calib_never_decides`; a first-class theorem needs a weights model
  and is Tier-2.

## Conformance bridge

`test-vectors/tier1.json` carries Tier-1 golden vectors derived from the
spec's pinned integer math (encode-once, `step`, `read`, `confAt`,
`isHard`, gate at τ=75, and the reinjected counterexample), frozen and
sha256-checked (`vectors_sha256`, canonical form with the field removed).
`conformance/conformance.py` is a real differential test:

* `ReferenceEngine` must match every vector (trace, boundary, gating);
* `ReinjectedEngine` must DIVERGE from the frozen trace from loop 1 on —
  the executable twin of `reinjection_differs`;
* `UngatedEngine` must violate conformance below the threshold — the
  basal 2.8.1 bug class, reproduced and asserted.

A deliberate divergence fails the suite; a silent engine change cannot
pass unnoticed.

```
python3 conformance/conformance.py --all   # 5 checks, exit 0
```

## Building

Requires [elan](https://github.com/leanprover/lean4); toolchain pinned in
`lean-toolchain` (currently `leanprover/lean4:v4.36.0`). Core Lean only:

```
lake build          # inside this directory
```

CI runs the same build in the `lean-spec` job of `.github/workflows/ci.yml`
and the conformance suite in `conformance` — a proof or a vector that no
longer holds fails the build loudly instead of silently drifting.

## Files

* `TypedDecision.lean` — root module
* `TypedDecision/Basic.lean` — response contract
* `TypedDecision/Defer.lean` — gating, deferral, hard-answer boundary
* `TypedDecision/Loop.lean` — looped engines (System 1.5)
* `test-vectors/tier1.json` — frozen Tier-1 vectors (sha256-pinned)
* `conformance/gen_vectors.py` — derives and freezes the vectors (run once)
* `conformance/conformance.py` — differential conformance suite
* `.github/workflows/ci.yml` — `lean-spec` + `conformance` jobs
