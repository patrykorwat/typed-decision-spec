#!/usr/bin/env python3
"""Phase B / B2+B4+B5+B6: Python reference adapter (issues #19, #21, #22, #23).

The Python twin of the Lean construction entry point designed in
`docs/phase-b-adapter-design.md` (#18):

    build (q : QType) (engine : EngineOutput) : ResponseFor q

`build(q, engine_output)` is keyed on the request's question type and the
dispatch key IS the return shape — one branch per QType. All six branches
produce responses: `choice`/`noul` (B2), `score` (B4), `act`/`tool` (B5)
and `multi` (B6). Design consequences mirrored here:

* Response objects carry NO `qtype` string field: the dispatch key selects
  the constructor, so a `noul`-labeled two-option `choice` response is
  unrepresentable BY CONSTRUCTION (Lean: `ResponseFor QType.noul =
  BinaryResponse`), not by a validator.
* `conf` and `argmax` are COMPUTED from the normalized distribution
  (`conf = max(probs)`, first-max argmax — the Python mirror of
  `binConf_is_top` / the `if 50 ≤ p then 0 else 1` rule), never supplied
  by the engine («computed, never supplied»).
* Strict validation mirrors the spec's structural mirrors: `type(x) is
  int` (bool rejected — `isinstance` is wrong, bool is an int subclass),
  bounds in BOTH directions, non-integer or out-of-vocabulary engine
  output is a REJECTION (exception), never silently coerced.
* `noul` accepts exactly the declared YES/NO pair (mirror of
  `declared_pair` in QTypes.lean); anything else is a rejection.
* `decide(calib, q, response)` is the honest call site: the same `q` that
  selected the branch and the same response object the branch produced go
  to the gate TOGETHER (the production twin of `gateLoop` reading the
  index from the structure — `wrong_loop_structural` /
  `wrong_type_structural`); the loop index travels IN the response object.
* `score` branch (B4, issue #21): the predicted `value` is COMPUTED from
  the engine-supplied distribution as the floor of the exact expected
  value (`exactEVnum / 100` — the Python mirror of the canonical path
  `scoreOfDist`), never supplied directly. The `confidence` is a SEPARATE
  supplied quantity on the [0,100] scale ("separate quantities, not
  functionally determined by one another"). `confidenceLoopIdx` = the
  engine's loop index — TRUSTED adapter metadata per the recorded
  provenance decision (`loops_are_metadata`): documented, NOT proved; the
  adapter must not imply loop-indexed provenance for the pairing.
* `decide_score(calib, response)` mirrors `gateScore` with the score
  calibration as ITS OWN object (`{"tau", "loopIdx"}` — separate from the
  binary `Calib`, no `qtype` field; it applies only to score responses,
  enforced by the response type at the call site). The payload is the
  VALUE (never the confidence — `gateScore_payload_is_value`); the gate
  abstains below the calibration's own threshold
  (`gateScore_defers_below`), at a wrong loop
  (`gateScore_wrong_loop_never_decides`), and with no calibration.
* `decide_score_result` mirrors `gateScoreResult` (`ScoreDecisionResult`):
  the decision plus BOTH loop indices travel with the result.
* `act` branch (B5, issue #22): the engine supplies the per-action cost
  distributions on the per-entry scale; the exact cost numerators
  (`exactCostNum` map) and the SELECTED action are COMPUTED — the minimum
  exact cost with the FIRST-DECLARED tie-break (`sel_min` + `sel_first`),
  never taken from the engine («computed, never supplied» extends to the
  whole selection: a floor-based selection could not distinguish
  same-floor/different-exact costs, so selection is by the exact
  numerator — the mirror of the recorded direction "selekcja po
  exactCostNum, NIGDY po floored expectedCost"). The confidence is a
  SEPARATE supplied quantity with its own loop (trusted metadata,
  `loops_are_metadata` precision — documented, not proved). Costs live on
  their OWN scale (`MAX_COST = 100`) per entry — a cost off the scale or
  a negative weight is a rejection.
* `tool` branch (B5): the selected next step is engine-supplied and
  validated by vocabulary membership (out-of-vocabulary = rejection,
  never coerced); NO tie-break rule (recorded design decision — the
  vocabulary carries no ordering quantity, act is the cost-bearing
  sibling). The confidence is separate, its loop trusted metadata.
* `decide_act(calib, response)` mirrors `gateAct`: the act calibration is
  ITS OWN object (`{"tau", "loopIdx"}` — a CONFIDENCE threshold, the gate
  compares τ with the response's confidence, never with any cost), the
  payload is the SELECTED ACTION (never a cost, never the confidence —
  `gateAct_payload_is_action`), and the gate abstains below τ
  (`gateAct_defers_below`), at a wrong loop
  (`gateAct_wrong_loop_never_decides`), and with no calibration. An act
  calibration gates only `ActResponse` objects (separate objects —
  mirror of Calib/ScoreCalib/ActCalib/ToolCalib separation).
  `decide_act_result` mirrors `gateActResult` (`ActDecisionResult`):
  the decision plus BOTH loop indices travel with the result.
* `decide_tool` / `decide_tool_result` mirror `gateTool` /
  `gateToolResult` (`ToolDecisionResult`, payload = the SELECTED TOOL)
  with the same abstention and type-guard semantics.
* `multi` branch (B6, issue #23): the engine supplies unique non-empty
  labels and one per-label binary distribution; each label's decision is
  a `BinaryResponse` mirror over the FIXED YES/NO pair with `conf =
  max(probs)` and the first-max argmax COMPUTED — never engine-supplied.
  The collection is per-label state, NOT one distribution over the power
  set, and NOT loop-bound (the Lean `BinaryResponse` carries no loop
  index; the loop layer is binary-only K = 2 by recorded design — no
  calibration object is invented here). Duplicate labels
  (`labels_nodup`), an empty collection (`labels_nonempty` — an empty
  multi collection is not a question) and a labels/decisions length
  mismatch (`len_match`) are rejections.
* `multi_set` mirrors the canonical update constructor `multiSet`: a
  `Fin`-range index (out-of-range and negative are rejections), the
  other labels' decisions left untouched — the structural half
  `multi_set_independent` proves; update locality, never a re-zip.
* `decide_multi(tau, response)` mirrors `gateMulti`: the pointwise lift
  of the shared gate over the per-label confidences at the collection's
  own threshold — payload `argmax` per deciding label, abstention per
  deferring label; below the threshold EVERY label defers
  (`gateMulti_defers_below`). The result is a STRUCTURE carrying the
  label–decision mapping (`MultiDecisionResult` with its own
  `len_match`), so the pairing travels with the result and the adapter
  never re-zips it.
* NO statistical-independence claim anywhere: the contract is «separate
  per-label distributions with update locality» — the marginals do not
  determine a joint distribution (`multi_set_independent` proves only
  the structural half), and no code path or result field suggests a
  joint model.

Engine output shape (`engine_output` dict): `{"loopIdx": int, "declared":
[str, ...], "probs": [int, ...]}` — the per-loop readout rendered as a
normalized integer distribution over the declared options, with the loop
index it was read at (binary branches). For `score`:
`{"loopIdx": int, "dist": [[value, weight], ...], "confidence": int}` —
the value distribution (weights normalized to 100, values on the
[0,100] scale), the confidence, and the loop the confidence was read at.
For `act`/`tool` see `_validated_act_output` / `_validated_tool_output`.
For `multi`: `{"labels": [str, ...], "probs": [[int, int], ...]}` — the
unique non-empty label list and one normalized two-entry binary
distribution per label (label i's distribution is the engine's own
per-label readout; no loop index — the collection is not loop-bound).
All Phase B slices are complete; the B2 slice touched no Lean module
and no frozen vector, and B4/B5/B6 add only adapter-side paths (the
frozen score/act/tool/multi fields already cover every gate branch — no
regeneration round needed).
"""

from dataclasses import dataclass

# the QTypes of Defer.lean, in declaration order
QTYPES = ("choice", "noul", "multi", "score", "act", "tool")
# all Phase B slices produce (B6 closed the last one, issue #23); the
# constant stays as the explicit slice-boundary record
LATER_SLICES = ()


def _require_int(x, name):
    """Strict integer check: `type(x) is int`, NOT isinstance — bool is a
    subclass of int in Python and `isinstance(True, int)` passes (mirror
    of Nat: True/False are not valid distribution entries or loop
    indices)."""
    if type(x) is not int:
        raise TypeError(
            f"{name} must be a strict integer (Nat), got {type(x).__name__}: {x!r}"
        )


def _require_bool_free_str_list(xs, name):
    if not isinstance(xs, list):
        raise TypeError(f"{name} must be a list, got {type(xs).__name__}")
    for x in xs:
        if type(x) is not str:
            raise TypeError(f"{name} entries must be str, got {x!r}")


def _validated_engine_output(engine_output):
    """Shared validation for every producing branch: strict ints, the
    [0,100] scale in BOTH directions, K >= 2, normalization, unique
    declared options, non-negative loop index (mirror of Nat)."""
    if not isinstance(engine_output, dict):
        raise TypeError(
            f"engine_output must be a dict, got {type(engine_output).__name__}"
        )
    for key in ("loopIdx", "declared", "probs"):
        if key not in engine_output:
            raise KeyError(f"engine_output missing {key!r}")
    _require_int(engine_output["loopIdx"], "loopIdx")
    if engine_output["loopIdx"] < 0:
        raise ValueError(
            f"negative loop index (mirror of Nat): {engine_output['loopIdx']}"
        )
    declared = engine_output["declared"]
    probs = engine_output["probs"]
    _require_bool_free_str_list(declared, "declared")
    if not isinstance(probs, list):
        raise TypeError(f"probs must be a list, got {type(probs).__name__}")
    for p in probs:
        _require_int(p, "probs entry")
        if not 0 <= p <= 100:
            raise ValueError(f"probs entry off the [0,100] scale: {p}")
    if len(declared) != len(probs):
        raise ValueError(
            f"declared/probs length mismatch: {len(declared)} != {len(probs)}"
        )
    if len(probs) < 2:
        raise ValueError(f"K < 2: not a question (k_ge_2), got {len(probs)} option(s)")
    if len(set(declared)) != len(declared):
        raise ValueError(f"declared options must be unique (declared_nodup): {declared}")
    if sum(probs) != 100:
        raise ValueError(f"probs must sum to 100 (sum_100), got {sum(probs)}")
    return engine_output["loopIdx"], declared, probs


@dataclass(frozen=True)
class ChoiceResponse:
    """Mirror of the shared `Response` core (Basic.lean) as produced by
    `binResponseOf`: K >= 2 declared options, normalized integer
    distribution, `conf = max(probs)` (binConf_is_top), first-max argmax.
    NO qtype field — the dispatch key chose this constructor."""

    declared: tuple
    probs: tuple
    argmax: int
    conf: int
    loopIdx: int


@dataclass(frozen=True)
class NoulResponse:
    """Mirror of `BinaryResponse` (QTypes.lean): the `noul` instance —
    exactly the declared YES/NO pair (`declared_pair`), confidence
    carrying its own loop index. NO qtype field."""

    declared: tuple
    probs: tuple
    argmax: int
    conf: int
    loopIdx: int


@dataclass(frozen=True)
class ScoreResponse:
    """Mirror of `ScoreResponse` (QTypes.lean): a scalar value on the
    explicit [0,100] scale plus a SEPARATE confidence with its own loop
    index. `value` is COMPUTED from the engine's distribution (floor of
    the exact expected value — the mirror of `scoreOfDist`), never
    supplied; `exact_num` is the computed exact numerator
    (`exactEVnum`, rational EV = exact_num / 100). `confidenceLoopIdx`
    is trusted adapter metadata (`loops_are_metadata`). NO qtype field."""

    value: int
    confidence: int
    confidenceLoopIdx: int
    exact_num: int


@dataclass(frozen=True)
class ScoreDecisionResult:
    """Mirror of `ScoreDecisionResult` (QTypes.lean): the decision plus
    BOTH loop indices — the response's confidence loop and the
    calibration's bound loop — so the pairing travels with the result."""

    value: int | None
    confLoopIdx: int
    calibLoopIdx: int


@dataclass(frozen=True)
class ActResponse:
    """Mirror of `ActResponse` (QTypes.lean): per-action cost
    distributions on the per-entry scale (`MAX_COST = 100` — each entry
    carries its own scale bound, mirrored by validation), the exact cost
    numerators EQUAL to the computed map (`nums_eq_map` — computed, never
    supplied), the SELECTED action which IS the minimal-exact-cost one
    with the FIRST-DECLARED tie-break (`sel_min` + `sel_first`), a
    separate confidence with its own loop index. The selection lives on
    the EXACT numerator, never on the floored expected cost. NO qtype
    field — the dispatch key chose this constructor."""

    actions: tuple
    costDists: tuple
    exactCostNums: tuple
    selected: str
    confidence: int
    confidenceLoopIdx: int


@dataclass(frozen=True)
class ActDecisionResult:
    """Mirror of `ActDecisionResult` (QTypes.lean): the decision plus
    BOTH loop indices — the response's confidence loop and the
    calibration's bound loop — so the pairing travels with the result."""

    action: str | None
    confLoopIdx: int
    calibLoopIdx: int


@dataclass(frozen=True)
class ToolResponse:
    """Mirror of `ToolResponse` (QTypes.lean): the selected next step from
    a declared duplicate-free non-empty vocabulary (`sel_mem`), with a
    confidence describing the trustworthiness of the choice itself and
    the confidence's own source loop. NO tie-break rule (recorded design
    decision: the vocabulary carries no ordering quantity — act is the
    cost-bearing sibling). NO qtype field."""

    tools: tuple
    selected: str
    confidence: int
    confidenceLoopIdx: int


@dataclass(frozen=True)
class ToolDecisionResult:
    """Mirror of `ToolDecisionResult` (QTypes.lean): the decision plus
    BOTH loop indices (mirror of `ActDecisionResult`)."""

    selected: str | None
    confLoopIdx: int
    calibLoopIdx: int


@dataclass(frozen=True)
class BinaryDecision:
    """Mirror of `BinaryResponse` (QTypes.lean): the formal binary
    decision — exactly two declared options carrying the YES/NO pair
    (`declared_pair`), the distribution and confidence as in the shared
    core (`conf = max(probs)` — computed, never supplied; first-max
    argmax). NO loop index: the Lean `BinaryResponse` carries none — a
    multi label's decision is per-label state, not loop-bound."""

    declared: tuple
    probs: tuple
    argmax: int
    conf: int


@dataclass(frozen=True)
class MultiResponse:
    """Mirror of `MultiResponse` (QTypes.lean): separate per-label binary
    decisions, one per UNIQUE non-empty label, position i of `decisions`
    being the decision FOR label i (`len_match` — the mapping travels in
    the object, an adapter cannot lose it by zipping). This is NOT one
    distribution over the power set and NOT loop-bound; the contract is
    «separate per-label distributions with update locality» — the
    marginals do NOT determine a joint distribution (no statistical
    independence is claimed or represented). NO qtype field."""

    labels: tuple
    decisions: tuple

    def __post_init__(self):
        if len(self.decisions) != len(self.labels):
            raise ValueError(
                f"len_match violated: {len(self.decisions)} decisions "
                f"for {len(self.labels)} labels"
            )


@dataclass(frozen=True)
class MultiDecisionResult:
    """Mirror of `MultiDecisionResult` (QTypes.lean): the gated collection
    — the label–decision mapping travels WITH the result (`len_match`
    re-checked, mirror of the Lean structure's own proof obligation), so
    the pairing is never re-zipped by a consumer. Each entry is the
    per-label gate payload (`"argmax"`) or `None` (that label deferred)."""

    labels: tuple
    decisions: tuple

    def __post_init__(self):
        if len(self.decisions) != len(self.labels):
            raise ValueError(
                f"len_match violated: {len(self.decisions)} decisions "
                f"for {len(self.labels)} labels"
            )


def _computed_fields(probs):
    """conf = max(probs), argmax = FIRST index attaining it (the mirror of
    `conf_is_top` / `argmax = if 50 ≤ p then 0 else 1` — deterministic
    tie-break at the 50/50 boundary, argmax 0)."""
    conf = max(probs)
    return conf, probs.index(conf)


def _build_choice(engine_output):
    """`choice` branch: the full shared Response core over the engine's
    declared options (Lean twin: `binResponseOf` at the loop's readout)."""
    loop, declared, probs = _validated_engine_output(engine_output)
    conf, argmax = _computed_fields(probs)
    return ChoiceResponse(
        declared=tuple(declared), probs=tuple(probs),
        argmax=argmax, conf=conf, loopIdx=loop,
    )


NOUL_PAIR = ("YES", "NO")


def _build_noul(engine_output):
    """`noul` branch: exactly the declared YES/NO pair (mirror of
    `declared_pair`); a different vocabulary — even a well-formed two-
    option one — is a REJECTION, never a relabeling."""
    loop, declared, probs = _validated_engine_output(engine_output)
    if tuple(declared) != NOUL_PAIR:
        raise ValueError(
            f"noul requires exactly the {list(NOUL_PAIR)} pair "
            f"(declared_pair), got {declared}"
        )
    conf, argmax = _computed_fields(probs)
    return NoulResponse(
        declared=tuple(declared), probs=tuple(probs),
        argmax=argmax, conf=conf, loopIdx=loop,
    )


def _validated_score_output(engine_output):
    """Validation for the `score` branch: strict ints everywhere (`type(x)
    is int`), the [0,100] scale in BOTH directions for the confidence and
    every dist value, non-negative loop index (mirror of Nat), weights
    normalized to 100 (mirror of `distSum dist = 100`), non-empty dist.
    Returns (loopIdx, dist, confidence)."""
    if not isinstance(engine_output, dict):
        raise TypeError(
            f"engine_output must be a dict, got {type(engine_output).__name__}"
        )
    for key in ("loopIdx", "dist", "confidence"):
        if key not in engine_output:
            raise KeyError(f"engine_output missing {key!r}")
    _require_int(engine_output["loopIdx"], "loopIdx")
    if engine_output["loopIdx"] < 0:
        raise ValueError(
            f"negative loop index (mirror of Nat): {engine_output['loopIdx']}"
        )
    dist = engine_output["dist"]
    if not isinstance(dist, list):
        raise TypeError(f"dist must be a list, got {type(dist).__name__}")
    if not dist:
        raise ValueError("dist must be non-empty (a score needs a distribution)")
    total = 0
    for entry in dist:
        if not isinstance(entry, (list, tuple)):
            raise TypeError(f"dist entries must be [value, weight], got {entry!r}")
        if len(entry) != 2:
            raise ValueError(f"dist entry must have exactly 2 fields, got {entry!r}")
        v, w = entry
        _require_int(v, "dist value")
        _require_int(w, "dist weight")
        if not 0 <= v <= 100:
            raise ValueError(f"dist value off the [0,100] scale: {v}")
        if w < 0:
            raise ValueError(f"negative dist weight (mirror of Nat): {w}")
        total += w
    if total != 100:
        raise ValueError(f"dist weights must sum to 100 (distSum), got {total}")
    confidence = engine_output["confidence"]
    _require_int(confidence, "confidence")
    if not 0 <= confidence <= 100:
        raise ValueError(
            f"confidence off the [0,100] scale (both directions): {confidence}"
        )
    return engine_output["loopIdx"], dist, confidence


def _build_score(engine_output):
    """`score` branch: the canonical construction path `scoreOfDist` — the
    predicted value IS the floor of the exact expected value of the
    engine's distribution (`exactEVnum / 100`, integer division), the
    confidence is carried separately WITH its source loop (trusted
    metadata). Nothing about the value is taken on faith from the engine:
    it is recomputed here and asserted by the contract's scale invariants."""
    loop, dist, confidence = _validated_score_output(engine_output)
    exact_num = sum(v * w for v, w in dist)
    return ScoreResponse(
        value=exact_num // 100,  # floor — the mirror of expectedValue
        confidence=confidence,
        confidenceLoopIdx=loop,
        exact_num=exact_num,
    )


# the act contract's OWN scale (mirror of MAX_COST in QTypes.lean); a
# separate notion from the calibration threshold — τ compares against the
# response's confidence, never against a cost
MAX_COST = 100


def _validated_confidence(engine_output):
    """Shared tail validation for the act/tool branches: the confidence is
    a SEPARATE supplied quantity on the [0,100] scale (strict int, both
    directions), the loop index a strict non-negative int (mirror of
    Nat). Returns (confidence, loopIdx)."""
    _require_int(engine_output["loopIdx"], "loopIdx")
    if engine_output["loopIdx"] < 0:
        raise ValueError(
            f"negative loop index (mirror of Nat): {engine_output['loopIdx']}"
        )
    confidence = engine_output["confidence"]
    _require_int(confidence, "confidence")
    if not 0 <= confidence <= 100:
        raise ValueError(
            f"confidence off the [0,100] scale (both directions): {confidence}"
        )
    return confidence, engine_output["loopIdx"]


def _validated_act_output(engine_output):
    """Validation for the `act` branch: actions non-empty and duplicate-
    free (`actions_nodup`, `actions_nonempty`), `len_match` between
    actions and costDists, each distribution's entries strict ints with
    the cost on the act's OWN scale in BOTH directions (0 ≤ cost ≤
    MAX_COST — per-entry scale, no negative weights, mirror of Nat) and
    the weights normalized to 100 (`distCostSum = 100`). Returns
    (loopIdx, actions, costDists, confidence)."""
    if not isinstance(engine_output, dict):
        raise TypeError(
            f"engine_output must be a dict, got {type(engine_output).__name__}"
        )
    for key in ("loopIdx", "actions", "costDists", "confidence"):
        if key not in engine_output:
            raise KeyError(f"engine_output missing {key!r}")
    actions = engine_output["actions"]
    _require_bool_free_str_list(actions, "actions")
    if not actions:
        raise ValueError("actions must be non-empty (actions_nonempty)")
    if len(set(actions)) != len(actions):
        raise ValueError(f"actions must be unique (actions_nodup): {actions}")
    costDists = engine_output["costDists"]
    if not isinstance(costDists, list):
        raise TypeError(f"costDists must be a list, got {type(costDists).__name__}")
    if len(costDists) != len(actions):
        raise ValueError(
            f"actions/costDists length mismatch (len_match): "
            f"{len(costDists)} != {len(actions)}"
        )
    for dist in costDists:
        if not isinstance(dist, list):
            raise TypeError(
                f"costDists entries must be lists of [cost, weight], got {dist!r}"
            )
        total = 0
        for entry in dist:
            if not isinstance(entry, (list, tuple)):
                raise TypeError(
                    f"cost distribution entries must be [cost, weight], got {entry!r}"
                )
            if len(entry) != 2:
                raise ValueError(
                    f"cost entry must have exactly 2 fields, got {entry!r}"
                )
            c, w = entry
            _require_int(c, "cost")
            _require_int(w, "weight")
            if not 0 <= c <= MAX_COST:
                raise ValueError(
                    f"cost off the act's own scale (both directions, "
                    f"MAX_COST = {MAX_COST}): {c}"
                )
            if w < 0:
                raise ValueError(f"negative weight (mirror of Nat): {w}")
            total += w
        if total != 100:
            raise ValueError(
                f"cost distribution weights must sum to 100 (distCostSum), got {total}"
            )
    confidence, loop = _validated_confidence(engine_output)
    return loop, actions, costDists, confidence


def _build_act(engine_output):
    """`act` branch: the exact cost numerators and the SELECTED action are
    COMPUTED (`costDists.map exactCostNum`, minimum, FIRST-declared
    tie-break) — never taken from the engine. The selection lives on the
    EXACT numerator: a floor-based selection could not distinguish
    same-floor/different-exact costs (the `floor_loses_information`
    witness [(1,50)] exact 50 vs [(4,20)] exact 80 — both floor to 0),
    so the mirror of the recorded direction holds: selection by
    `exactCostNum`, never by floored `expectedCost`."""
    loop, actions, costDists, confidence = _validated_act_output(engine_output)
    exact_nums = [sum(c * w for c, w in dist) for dist in costDists]
    # FIRST index attaining the minimum: the first-declared tie-break
    # (sel_min + sel_first, deterministic — abstention on ties would
    # break the gate's monotonicity)
    best = exact_nums.index(min(exact_nums))
    return ActResponse(
        actions=tuple(actions),
        costDists=tuple(tuple(dist) for dist in costDists),
        exactCostNums=tuple(exact_nums),
        selected=actions[best],
        confidence=confidence,
        confidenceLoopIdx=loop,
    )


def _validated_tool_output(engine_output):
    """Validation for the `tool` branch: the vocabulary non-empty and
    duplicate-free (`tools_nodup`, `tools_nonempty`), the engine-supplied
    selection a MEMBER of it (`sel_mem` — out-of-vocabulary is a
    rejection, never a coercion), the confidence separate on the
    [0,100] scale, the loop index a strict non-negative int. Returns
    (loopIdx, tools, selected, confidence)."""
    if not isinstance(engine_output, dict):
        raise TypeError(
            f"engine_output must be a dict, got {type(engine_output).__name__}"
        )
    for key in ("loopIdx", "tools", "selected", "confidence"):
        if key not in engine_output:
            raise KeyError(f"engine_output missing {key!r}")
    tools = engine_output["tools"]
    _require_bool_free_str_list(tools, "tools")
    if not tools:
        raise ValueError("tools must be non-empty (tools_nonempty)")
    if len(set(tools)) != len(tools):
        raise ValueError(f"tools must be unique (tools_nodup): {tools}")
    selected = engine_output["selected"]
    if not isinstance(selected, str):
        raise TypeError(
            f"selected must be str, got {type(selected).__name__}: {selected!r}"
        )
    if selected not in tools:
        raise ValueError(
            f"selected tool {selected!r} is out of the declared vocabulary "
            f"(sel_mem): {tools}"
        )
    confidence, loop = _validated_confidence(engine_output)
    return loop, tools, selected, confidence


def _build_tool(engine_output):
    """`tool` branch: the selected next step is engine-supplied and
    validated by vocabulary membership — there is NO ordering quantity to
    compute a selection from (recorded design decision: no tie-break
    rule, the vocabulary distinctness makes the selection's identity
    unambiguous)."""
    loop, tools, selected, confidence = _validated_tool_output(engine_output)
    return ToolResponse(
        tools=tuple(tools),
        selected=selected,
        confidence=confidence,
        confidenceLoopIdx=loop,
    )


def _validated_multi_output(engine_output):
    """Validation for the `multi` branch: labels non-empty and
    duplicate-free (`labels_nonempty`, `labels_nodup` — an empty
    collection is NOT a question), every label a str, `len_match` between
    labels and per-label distributions, each distribution exactly two
    entries (the binary contract), strict ints on the [0,100] scale in
    BOTH directions summing to 100. Returns (labels, probs)."""
    if not isinstance(engine_output, dict):
        raise TypeError(
            f"engine_output must be a dict, got {type(engine_output).__name__}"
        )
    for key in ("labels", "probs"):
        if key not in engine_output:
            raise KeyError(f"engine_output missing {key!r}")
    labels = engine_output["labels"]
    _require_bool_free_str_list(labels, "labels")
    if not labels:
        raise ValueError(
            "labels must be non-empty (labels_nonempty: an empty multi "
            "collection is not a question)"
        )
    if len(set(labels)) != len(labels):
        raise ValueError(f"labels must be unique (labels_nodup): {labels}")
    probs = engine_output["probs"]
    if not isinstance(probs, list):
        raise TypeError(f"probs must be a list, got {type(probs).__name__}")
    if len(probs) != len(labels):
        raise ValueError(
            f"labels/probs length mismatch (len_match): "
            f"{len(probs)} != {len(labels)}"
        )
    for dist in probs:
        if not isinstance(dist, list):
            raise TypeError(
                f"per-label distributions must be lists, got {dist!r}"
            )
        if len(dist) != 2:
            raise ValueError(
                f"each label's distribution must have exactly 2 entries "
                f"(the binary contract), got {len(dist)}: {dist!r}"
            )
        total = 0
        for p in dist:
            _require_int(p, "per-label probs entry")
            if not 0 <= p <= 100:
                raise ValueError(
                    f"per-label probs entry off the [0,100] scale "
                    f"(both directions): {p}"
                )
            total += p
        if total != 100:
            raise ValueError(
                f"per-label probs must sum to 100 (sum_100), got {total}"
            )
    return labels, probs


def _build_multi(engine_output):
    """`multi` branch: one `BinaryResponse` mirror per label over the
    FIXED YES/NO pair, each label's `conf`/`argmax` COMPUTED from ITS OWN
    distribution (`conf = max(probs)`, first-max argmax) — never
    engine-supplied. The collection is per-label state, not loop-bound
    and not a joint distribution over the power set."""
    labels, probs = _validated_multi_output(engine_output)
    decisions = []
    for dist in probs:
        conf, argmax = _computed_fields(dist)
        decisions.append(BinaryDecision(
            declared=NOUL_PAIR, probs=tuple(dist),
            argmax=argmax, conf=conf,
        ))
    return MultiResponse(labels=tuple(labels), decisions=tuple(decisions))


def build(q, engine_output):
    """Keyed dispatch: `ResponseFor q` — the return shape is determined by
    the request's question type, the SAME `q` the request arrived with."""
    if q == "choice":
        return _build_choice(engine_output)
    if q == "noul":
        return _build_noul(engine_output)
    if q == "score":
        return _build_score(engine_output)
    if q == "act":
        return _build_act(engine_output)
    if q == "tool":
        return _build_tool(engine_output)
    if q == "multi":
        return _build_multi(engine_output)
    if q in LATER_SLICES:
        raise NotImplementedError(
            f"q={q!r}: a later Phase B slice (B6), not this one"
        )
    raise ValueError(f"unknown question type: {q!r} (expected one of {QTYPES})")


def decide(calib, q, response):
    """The honest gate call site (mirror of gateLoop at
    `gateLoop_eq_gateCalib`): the SAME `q` that dispatched the branch and
    the SAME response object it produced go to the gate together; the loop
    index is read FROM the response object, not from a caller argument.
    `calib` mirrors `Calib` ({qtype, loopIdx, tau}); `None` mirrors
    `gateOptCalib none` (no calibration record — no decision)."""
    if calib is None:
        return None
    if not isinstance(calib, dict):
        raise TypeError(f"calib must be a dict or None, got {type(calib).__name__}")
    for key in ("qtype", "loopIdx", "tau"):
        if key not in calib:
            raise KeyError(f"calib missing {key!r}")
    _require_int(calib["loopIdx"], "calib loopIdx")
    _require_int(calib["tau"], "calib tau")
    if not 0 <= calib["tau"] <= 100:
        raise ValueError(f"calib tau off the [0,100] scale: {calib['tau']}")
    if not isinstance(response, (ChoiceResponse, NoulResponse)):
        raise TypeError(
            "the binary Calib gates only binary responses (separate "
            f"objects), got {type(response).__name__}"
        )
    if calib["qtype"] != q or calib["loopIdx"] != response.loopIdx:
        return None  # wrong type or wrong loop: never decides
    return "argmax" if calib["tau"] <= response.conf else None


def _validated_score_calib(calib):
    """The score calibration is ITS OWN object (mirror of `ScoreCalib` —
    separate from the binary `Calib`): `{"tau": int, "loopIdx": int}`, no
    `qtype` field; `threshold_le_100` is ONLY the structural scale bound
    (whether τ is statistically calibrated is outside this model, same
    precision as `Calib.certified`)."""
    if not isinstance(calib, dict):
        raise TypeError(f"calib must be a dict, got {type(calib).__name__}")
    for key in ("tau", "loopIdx"):
        if key not in calib:
            raise KeyError(f"score calib missing {key!r}")
    _require_int(calib["tau"], "score calib tau")
    _require_int(calib["loopIdx"], "score calib loopIdx")
    if not 0 <= calib["tau"] <= 100:
        raise ValueError(
            f"score calib tau off the [0,100] scale: {calib['tau']}"
        )
    if calib["loopIdx"] < 0:
        raise ValueError(
            f"negative calib loop index (mirror of Nat): {calib['loopIdx']}"
        )
    return calib["tau"], calib["loopIdx"]


def decide_score(calib, response):
    """The honest score gate call site (mirror of `gateScore`): the score
    calibration applies ONLY to score responses (enforced by the response
    type — the calibration is its own object), the loop index is read FROM
    the response's `confidenceLoopIdx`, and the payload is the VALUE,
    never the confidence. `None` calib mirrors "no calibration record"."""
    if calib is None:
        return None
    if not isinstance(response, ScoreResponse):
        raise TypeError(
            "a score calibration gates only ScoreResponse objects "
            f"(separate objects), got {type(response).__name__}"
        )
    tau, calib_loop = _validated_score_calib(calib)
    if calib_loop != response.confidenceLoopIdx:
        return None  # wrong loop: never decides (gateScore_wrong_loop)
    return response.value if tau <= response.confidence else None


def decide_score_result(calib, response):
    """Mirror of `gateScoreResult` (`ScoreDecisionResult`): the gate
    outcome plus BOTH loop indices — the response's confidence loop and
    the calibration's bound loop — so the conf-loop ↔ calib-loop pairing
    travels with the result even on abstention. Requires a score
    calibration (Lean's `gateScoreResult` takes a concrete `ScoreCalib`;
    the no-record case is `decide_score(None, …)`)."""
    if not isinstance(response, ScoreResponse):
        raise TypeError(
            "a score calibration gates only ScoreResponse objects "
            f"(separate objects), got {type(response).__name__}"
        )
    tau, calib_loop = _validated_score_calib(calib)
    return ScoreDecisionResult(
        value=response.value if (
            calib_loop == response.confidenceLoopIdx and tau <= response.confidence
        ) else None,
        confLoopIdx=response.confidenceLoopIdx,
        calibLoopIdx=calib_loop,
    )


def _validated_act_tool_calib(calib, name):
    """The act/tool calibration is ITS OWN object (mirror of `ActCalib` /
    `ToolCalib` — separate from the binary `Calib` and from `ScoreCalib`):
    `{"tau": int, "loopIdx": int}`, no `qtype` field. τ is a CONFIDENCE
    threshold (`threshold_le_100`, ≤ 100 — the gate compares τ with the
    response's confidence, NEVER with a cost; the cost scale MAX_COST is
    a separate notion, unbound here)."""
    if not isinstance(calib, dict):
        raise TypeError(f"{name} must be a dict, got {type(calib).__name__}")
    for key in ("tau", "loopIdx"):
        if key not in calib:
            raise KeyError(f"{name} missing {key!r}")
    _require_int(calib["tau"], f"{name} tau")
    _require_int(calib["loopIdx"], f"{name} loopIdx")
    if not 0 <= calib["tau"] <= 100:
        raise ValueError(f"{name} tau off the [0,100] scale: {calib['tau']}")
    if calib["loopIdx"] < 0:
        raise ValueError(
            f"negative calib loop index (mirror of Nat): {calib['loopIdx']}"
        )
    return calib["tau"], calib["loopIdx"]


def decide_act(calib, response):
    """The honest act gate call site (mirror of `gateAct`): the act
    calibration applies ONLY to act responses (enforced by the response
    type — separate objects), the loop index is read FROM the response's
    `confidenceLoopIdx`, and the payload is the SELECTED ACTION, never a
    cost and never the confidence (`gateAct_payload_is_action`). `None`
    calib mirrors "no calibration record"."""
    if calib is None:
        return None
    if not isinstance(response, ActResponse):
        raise TypeError(
            "an act calibration gates only ActResponse objects "
            f"(separate objects), got {type(response).__name__}"
        )
    tau, calib_loop = _validated_act_tool_calib(calib, "act calib")
    if calib_loop != response.confidenceLoopIdx:
        return None  # wrong loop: never decides (gateAct_wrong_loop)
    return response.selected if tau <= response.confidence else None


def decide_act_result(calib, response):
    """Mirror of `gateActResult` (`ActDecisionResult`): the gate outcome
    plus BOTH loop indices — the response's confidence loop and the
    calibration's bound loop — so the conf-loop ↔ calib-loop pairing
    travels with the result even on abstention. Requires an act
    calibration (Lean's `gateActResult` takes a concrete `ActCalib`; the
    no-record case is `decide_act(None, …)`)."""
    if not isinstance(response, ActResponse):
        raise TypeError(
            "an act calibration gates only ActResponse objects "
            f"(separate objects), got {type(response).__name__}"
        )
    tau, calib_loop = _validated_act_tool_calib(calib, "act calib")
    return ActDecisionResult(
        action=response.selected if (
            calib_loop == response.confidenceLoopIdx and tau <= response.confidence
        ) else None,
        confLoopIdx=response.confidenceLoopIdx,
        calibLoopIdx=calib_loop,
    )


def decide_tool(calib, response):
    """The honest tool gate call site (mirror of `gateTool`): the tool
    calibration applies ONLY to tool responses (separate objects), the
    loop index is read FROM the response's `confidenceLoopIdx`, and the
    payload is the SELECTED TOOL, never the confidence
    (`gateTool_payload_is_tool`). `None` calib mirrors "no calibration
    record"."""
    if calib is None:
        return None
    if not isinstance(response, ToolResponse):
        raise TypeError(
            "a tool calibration gates only ToolResponse objects "
            f"(separate objects), got {type(response).__name__}"
        )
    tau, calib_loop = _validated_act_tool_calib(calib, "tool calib")
    if calib_loop != response.confidenceLoopIdx:
        return None  # wrong loop: never decides (gateTool_wrong_loop)
    return response.selected if tau <= response.confidence else None


def decide_tool_result(calib, response):
    """Mirror of `gateToolResult` (`ToolDecisionResult`): the gate outcome
    plus BOTH loop indices (mirror of `decide_act_result`)."""
    if not isinstance(response, ToolResponse):
        raise TypeError(
            "a tool calibration gates only ToolResponse objects "
            f"(separate objects), got {type(response).__name__}"
        )
    tau, calib_loop = _validated_act_tool_calib(calib, "tool calib")
    return ToolDecisionResult(
        selected=response.selected if (
            calib_loop == response.confidenceLoopIdx and tau <= response.confidence
        ) else None,
        confLoopIdx=response.confidenceLoopIdx,
        calibLoopIdx=calib_loop,
    )


def multi_set(response, i, decision):
    """Mirror of the canonical update constructor `multiSet` (QTypes.lean):
    replace label i's decision, keeping the collection well-formed — the
    label list and every OTHER label's decision are left untouched
    (update locality, the structural half `multi_set_independent` proves;
    the statistical half is NOT claimed). The index is a `Fin` over the
    label list: strict int (`type(x) is int` — bool is not an index),
    `0 <= i < len(labels)` — pointing at a non-existent label or a
    negative index is a REJECTION, never a silent wrap. The replacement
    must be a `BinaryDecision` (the per-label binary contract)."""
    if not isinstance(response, MultiResponse):
        raise TypeError(
            "multi_set updates only MultiResponse objects, got "
            f"{type(response).__name__}"
        )
    if not isinstance(decision, BinaryDecision):
        raise TypeError(
            "the replacement must be a BinaryDecision (the per-label "
            f"binary contract), got {type(decision).__name__}"
        )
    _require_int(i, "update index")
    if not 0 <= i < len(response.labels):
        raise ValueError(
            f"update index {i} out of the Fin range for "
            f"{len(response.labels)} labels (phantom update unrepresentable)"
        )
    return MultiResponse(
        labels=response.labels,
        decisions=response.decisions[:i] + (decision,) + response.decisions[i + 1:],
    )


def decide_multi(tau, response):
    """The honest multi gate call site (mirror of `gateMulti`): the
    pointwise lift of the shared gate over each label's OWN confidence at
    the collection's own threshold — the payload is `"argmax"` for a
    deciding label, `None` for a deferring one; below the threshold EVERY
    label defers (`gateMulti_defers_below`). There is NO loop binding and
    NO calibration object: the Lean `gateMulti` takes the bare threshold
    (the loop layer is binary-only K = 2 — generalizing the structural
    loop layer to collections is its own recorded open question, no
    calibration is invented here). The result carries the label–decision
    mapping as a structure (`MultiDecisionResult`), never a re-zipped
    pairing."""
    _require_int(tau, "multi gate tau")
    if not 0 <= tau <= 100:
        raise ValueError(f"multi gate tau off the [0,100] scale: {tau}")
    if not isinstance(response, MultiResponse):
        raise TypeError(
            "the multi gate gates only MultiResponse objects (separate "
            f"objects), got {type(response).__name__}"
        )
    return MultiDecisionResult(
        labels=response.labels,
        decisions=tuple(
            "argmax" if tau <= d.conf else None for d in response.decisions
        ),
    )
