# Phase B design note: production adapter request → `ResponseFor` (#18)

Status: **design (spike)** — no production code in this commit. This note is
the design deliverable of #18; implementation sub-issues are opened per step
from it, each BEFORE its code.

## Problem

`ResponseFor : QType → Type` (Phase A, `30ed12a`) makes the assignment of a
response shape to a question type a typed object: `ResponseFor QType.act =
ActResponse` etc., all six dispatch theorems `rfl`. What Phase A deliberately
does NOT close is the production side: a real engine's request/response cycle
still has to be mapped onto the contracts, and the current canonical loop
constructor `binLoopResponse r F h0 t q` carries `q` as a *field* (`LoopResponse.qtype`)
— the recorded Tier-1 laxity: the same function can mislabel `qtype` (e.g.
`noul` over a two-option `choice` vocabulary) because `q` is supplied, not
dispatched. The review guidance for Phase B: **the adapter must return
`ResponseFor q` for the SAME `q` it received the request with.**

## Design

### 1. Pairing is enforced by dispatch, not by a field

The adapter's construction entry point is keyed on the request's `q` and the
dispatch key IS the return type:

```
build (q : QType) (engine : EngineOutput) : ResponseFor q
```

with one construction branch per `QType` (choice/noul/multi/score/act/tool).
Consequences, mirrored in the Python reference adapter:

* The response objects carry **no `qtype` string field**. A `noul`-labeled
  two-option `choice` response becomes unrepresentable not by a validator but
  by construction: you cannot obtain a `BinaryResponse` from the `choice`
  branch, and the gate consumes the object the SAME dispatch produced.
* The gate call site receives `(q, build q engine)` from one call path —
  there is no second `q` for the caller to disagree with. This is the
  production twin of `gateLoop` reading the index from the structure
  (`wrong_loop_structural` / `wrong_type_structural`): the pairing travels in
  the object, the gate never re-derives it from an argument.
* In Lean terms this is `match q with …` returning the family member —
  definitional dispatch, no wrapper, no weakening of the per-contract
  invariants (Phase A's constraint stands: no flattened sum).

### 2. What the adapter supplies per contract

| qtype | construction obligations the adapter must satisfy |
|---|---|
| choice | normalized integer distribution over K ≥ 2 declared options, `conf = max p (100−p)` (via `Response`'s invariants) |
| noul | exactly the declared YES/NO pair (`declared_pair`), confidence with its own loop |
| multi | unique non-empty labels (`labels_nodup`, `labels_nonempty`), `Fin`-indexed per-label distributions — the adapter recomputes and asserts uniqueness; it never supplies the pairing separately |
| score | `ScoreResponse` with `confidenceLoopIdx` set from the loop the calibration was fitted at (trusted adapter metadata — `loops_are_metadata` is the recorded provenance decision), value on the [0,100] scale |
| act | per-action cost distributions on the per-entry scale, `exactCostNums` recomputed («computed, never supplied»), minimal exact cost, first-declared tie-break — the certificates `actOfDists` demands are recomputed and asserted, never taken from the engine |
| tool | selected tool ∈ declared duplicate-free non-empty vocabulary, confidence with its own loop |

Strict validation mirrors the spec's structural mirrors: `type(x) is int`
(bool is not an int), bounds checked in both directions, non-integer or
out-of-vocabulary engine output is a rejection, never silently coerced.

### 3. First adapter slice: `choice`/`noul` (the binary loop path)

Rationale:

* the loop layer (`Loop.lean`) is **binary-only (K = 2)** by recorded design —
  the structural loop machinery (`LoopResponse`, `gateLoop`, per-loop readout
  provenance) exists only for the binary contracts;
* the canonical constructor + provenance theorems (`binLoopResponse_loopIdx`,
  `binLoopResponse_response`) already pin the loop/index pairing the adapter
  must reproduce;
* the conformance bridge already exercises this path three-way (Lean export,
  frozen vectors, Python engines), so adapter output has an existing
  differential target.

`score` is the second step (scalar, no loop layer yet — `ScoreCalib` binds the
loop as trusted metadata), then `act`/`tool`, then `multi` (largest surface:
per-label structure + update locality). Each extension is its own sub-issue.

### 4. Conformance report shape (what is validated vs reported)

Per request the adapter emits a record:

* `qtype` — the dispatch key (same value that selected the contract);
* `loopIdx` — the loop the response and (for score/act/tool) the confidence
  came from;
* gate outcome — `none` (abstention: below τ, wrong loop, no calibration) or
  the payload (`argmax` / value / action / tool), computed by the canonical
  gate of that contract;
* provenance class — whether the case matches a frozen vector (validated
  three-way: Lean == frozen == adapter) or is unpinned (reported only).

Engine quality (accuracy, ECE, selection correctness for act/tool) is
**evaluation data outside this repository** — reported, never encoded as a
Lean claim; the formal-spec boundary of the README stays.

### 5. Risks / open questions

* **Score confidence provenance** is metadata, not a proof
  (`confidenceLoopIdx` is trusted adapter input; `loops_are_metadata` records
  the decision, full loop-indexed provenance deliberately deferred). The
  adapter must document where it takes that index from and must not imply the
  pairing is proved.
* **Act certificates at scale**: `actOfDists` requires the caller to prove
  normalization, minimality and first-declared tie-break. The mirror recomputes
  and asserts; a real engine supplying unnormalized weights or a non-minimal
  selection is a rejection, not a repair.
* **Multi update locality**: the adapter must keep per-label updates local
  (one label's update must not touch other labels' distributions) — this is
  the structural half `multi_set_independent` proves; the statistical half is
  NOT claimed and the report must not suggest otherwise.
* **Loop layer generalization**: extending the structural loop layer beyond
  K = 2 (needed for score/act/tool/multi loop binding at the structural
  level) is its own design question and gets its own issue if attempted —
  this slice does not touch `Loop.lean`.
* **No generic gate over the family** in Phase B either: the per-contract
  gates stay canonical (payload/provenance types differ by design).

## Implementation plan (sub-issues, each before its code)

1. **B1 — this design note** (done by the commit carrying it).
2. **B2 — Python reference adapter skeleton** (`build(q, engine_output)` keyed
   dispatch, strict validation, rejection tests; `choice`/`noul` slice).
3. **B3 — bridge integration**: adapter output feeding the conformance report,
   differential against the frozen vectors; report shape per §4.
4. **B4 — score**, **B5 — act/tool**, **B6 — multi** slices, each with its own
   frozen-vector additions through the canonical regeneration procedure
   (one regeneration per round).
