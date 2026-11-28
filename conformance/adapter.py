#!/usr/bin/env python3
"""Phase B / B2: Python reference adapter skeleton (issue #19).

The Python twin of the Lean construction entry point designed in
`docs/phase-b-adapter-design.md` (#18):

    build (q : QType) (engine : EngineOutput) : ResponseFor q

`build(q, engine_output)` is keyed on the request's question type and the
dispatch key IS the return shape — one branch per QType. In this slice only
`choice` and `noul` produce responses (other branches raise
NotImplementedError: the slice boundary is explicit, never a silent
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

Engine output shape (`engine_output` dict): `{"loopIdx": int, "declared":
[str, ...], "probs": [int, ...]}` — the per-loop readout rendered as a
normalized integer distribution over the declared options, with the loop
index it was read at. This slice touches no Lean module and no frozen
vector (bridge integration is B3, score/act/tool/multi are B4–B6).
"""

from dataclasses import dataclass

# the QTypes of Defer.lean, in declaration order
QTYPES = ("choice", "noul", "multi", "score", "act", "tool")
# later Phase B slices (B4–B6); multi is B6, score B4, act/tool B5
LATER_SLICES = ("multi", "score", "act", "tool")


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


def build(q, engine_output):
    """Keyed dispatch: `ResponseFor q` — the return shape is determined by
    the request's question type, the SAME `q` the request arrived with."""
    if q == "choice":
        return _build_choice(engine_output)
    if q == "noul":
        return _build_noul(engine_output)
    if q in LATER_SLICES:
        raise NotImplementedError(
            f"q={q!r}: a later Phase B slice (B4–B6), not this one"
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
    if calib["qtype"] != q or calib["loopIdx"] != response.loopIdx:
        return None  # wrong type or wrong loop: never decides
    return "argmax" if calib["tau"] <= response.conf else None
