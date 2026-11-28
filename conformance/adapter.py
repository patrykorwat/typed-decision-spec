#!/usr/bin/env python3
"""Phase B / B2+B4: Python reference adapter (issues #19, #21).

The Python twin of the Lean construction entry point designed in
`docs/phase-b-adapter-design.md` (#18):

    build (q : QType) (engine : EngineOutput) : ResponseFor q

`build(q, engine_output)` is keyed on the request's question type and the
dispatch key IS the return shape — one branch per QType. In this slice
`choice`, `noul` (B2) and `score` (B4) produce responses (other branches
raise NotImplementedError: the slice boundary is explicit, never a silent
fallback). Design consequences mirrored here:

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
  `decide_score_result` mirrors `gateScoreResult` (`ScoreDecisionResult`):
  the decision plus BOTH loop indices travel with the result.

Engine output shape (`engine_output` dict): `{"loopIdx": int, "declared":
[str, ...], "probs": [int, ...]}` — the per-loop readout rendered as a
normalized integer distribution over the declared options, with the loop
index it was read at (binary branches). For `score`:
`{"loopIdx": int, "dist": [[value, weight], ...], "confidence": int}` —
the value distribution (weights normalized to 100, values on the
[0,100] scale), the confidence, and the loop the confidence was read at.
The B2 slice touched no Lean module and no frozen vector; B4 adds only
the adapter-side path (the frozen score fields already cover every gate
branch — no regeneration round needed).
"""

from dataclasses import dataclass

# the QTypes of Defer.lean, in declaration order
QTYPES = ("choice", "noul", "multi", "score", "act", "tool")
# later Phase B slices (B5–B6); multi is B6, act/tool B5 — score moved to
# the producing branches in B4 (issue #21)
LATER_SLICES = ("multi", "act", "tool")


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


def build(q, engine_output):
    """Keyed dispatch: `ResponseFor q` — the return shape is determined by
    the request's question type, the SAME `q` the request arrived with."""
    if q == "choice":
        return _build_choice(engine_output)
    if q == "noul":
        return _build_noul(engine_output)
    if q == "score":
        return _build_score(engine_output)
    if q in LATER_SLICES:
        raise NotImplementedError(
            f"q={q!r}: a later Phase B slice (B5–B6), not this one"
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
