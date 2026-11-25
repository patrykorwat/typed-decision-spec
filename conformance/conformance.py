#!/usr/bin/env python3
"""Conformance bridge: Tier-1 golden vectors vs. the spec and the engines.

Three-way differential test (the formal half runs in Lean):

  1. FROZEN vectors (test-vectors/tier1.json, sha256-pinned) — the datum.
  2. LEAN export (conformance/ExportVectors.lean, run via `lake env lean
     --run`) — computes the expected values FROM the proved definitions
     (`runBin`, `isHard` via its Decidable instance, the shared `gateP`,
     and the pinned `spec_T`). Lean == frozen closes the "generator
     implements its own math" gap.
  3. PYTHON mirror engines — ReferenceEngine must match; ReinjectedEngine
     (re-injects tokens) must DIVERGE (twin of `reinjection_differs`);
     UngatedEngine (no gate outside act/tool) must VIOLATE below the
     calibration threshold for every affected question type (the
     REPORTED basal 2.8.1 finding class); a calibration fitted at loop 3
     must not gate loop 8 (twin of `wrong_loop_never_decides`).

Scope note: the three-way check covers the ITERATIVE part of the pipeline
(trace, isHard, gate). `encode` (sha256 → h0) exists only in Python and
is asserted against the frozen h0 — the Lean side receives H0 precomputed
(sha256 is not in Lean core).

Run:  python3 conformance/conformance.py            # all tests
      python3 conformance/conformance.py --fast     # skip the Lean export
      (or: pytest conformance/conformance.py)
"""

import argparse
import hashlib
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
VECTORS_PATH = REPO_ROOT / "test-vectors" / "tier1.json"
EXPORT_PATH = REPO_ROOT / "conformance" / "ExportVectors.lean"
SPEC_T = 8  # the pinned budget (Loop.lean: spec_T) — frozen must match
HARD_ANSWER_THRESHOLD_K2 = 75  # isHard_K2 boundary (EVALUATION, Defer.lean)
GATED_TYPES = ("act", "tool")
AFFECTED_TYPES = ("choice", "noul", "score", "multi")


def load_vectors() -> dict:
    raw = json.loads(VECTORS_PATH.read_text(encoding="utf-8"))
    pinned = raw.pop("vectors_sha256")
    canon = json.dumps(
        raw, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode()
    got = hashlib.sha256(canon).hexdigest()
    assert got == pinned, f"vector integrity: sha256 mismatch ({got} != {pinned})"
    return raw


V = load_vectors()
PIN = V["pin"]
# the two thresholds are SEMANTICALLY DISTINCT even when numerically equal
CALIBRATION_THRESHOLD = PIN["calibration_threshold"]


def _step(h: int) -> int:
    return (PIN["A"] * h + PIN["B"]) % PIN["M"]


def _read(t: int, h: int) -> int:
    return (PIN["W"] * h + PIN["R"] * t) % 100


def _is_hard(k: int, conf: int) -> bool:
    """Mirror of the spec's isHard (Defer.lean)."""
    return 2 * k * conf >= 100 * (k + 1)


def _gate_p(tau: int, conf: int) -> str:
    """Mirror of the spec's shared gate predicate gateP (Defer.lean)."""
    return "argmax" if tau <= conf else "none"


def encode_once(state: str) -> int:
    """Tokens are encoded ONCE into h0 (Loop.lean: iter F t h0)."""
    return int(hashlib.sha256(state.encode()).hexdigest()[:8], 16) % PIN["M"]


def lean_export() -> dict:
    """Run the spec's own definitions (ExportVectors.lean) on the pin."""
    pin = PIN
    args = [str(pin["A"]), str(pin["B"]), str(pin["M"]), str(pin["W"]),
            str(pin["R"]), str(V["h0"]), str(CALIBRATION_THRESHOLD)]
    try:
        proc = subprocess.run(
            ["lake", "env", "lean", "--run", str(EXPORT_PATH)] + args,
            capture_output=True, text=True, cwd=REPO_ROOT, timeout=300,
        )
    except FileNotFoundError as e:
        raise AssertionError(f"lake not found — build the Lean project first: {e}")
    except subprocess.TimeoutExpired as e:
        raise AssertionError(f"Lean export timed out after 300s: {e}")
    if proc.returncode != 0:
        raise AssertionError(f"Lean export failed (rc={proc.returncode}): {proc.stderr[-2000:]}")
    try:
        return json.loads(proc.stdout)
    except json.JSONDecodeError as e:
        raise AssertionError(f"Lean export produced invalid JSON ({e}): {proc.stdout[:500]}")


class ReferenceEngine:
    """conforming gate via gateP: decide iff conf >= tau, EVERY type."""

    name = "reference"

    def __init__(self, state: str) -> None:
        self.h0 = encode_once(state)

    def _h(self, t: int) -> int:
        h = self.h0
        for _ in range(t):
            h = _step(h)
        return h

    def raw_at(self, t: int) -> int:
        """The RAW per-loop readout (Lean's `rd t h`) — the same quantity
        `reinjectedRun` maps, so raw-vs-raw comparisons are honest."""
        return _read(t, self._h(t))

    def probs_at(self, t: int) -> list:
        """The full binary distribution at loop t, from THIS engine's own
        raw readout — the independent Python mirror of the exported
        `probs_trace` (binProbsOf at the loop's own readout)."""
        p = self.raw_at(t)
        return [p, 100 - p]

    def conf_at(self, t: int) -> int:
        return max(_read(t, self._h(t)), 100 - _read(t, self._h(t)))

    def gate(self, conf: int, tau: int, qtype: str = "choice") -> str:
        return _gate_p(tau, conf)


class ReinjectedEngine(ReferenceEngine):
    """WRONG engine: h_{t+1} = step(h_t) + tokens — a different model.
    Its trace is the SCALAR per-loop RAW readout (mirror of Lean's
    `reinjectedRun`, which maps `rd`, not the confidence) — raw-vs-raw
    with `ReferenceEngine.raw_at` is the honest divergence test."""

    name = "reinjected"

    def _h(self, t: int) -> int:
        h = self.h0
        for _ in range(t):
            h = _step(h) + self.h0
        return h

    def raw_at(self, t: int) -> int:
        return _read(t, self._h(t))

    def conf_at(self, t: int) -> int:
        return _read(t, self._h(t))


class SwappedReadoutEngine(ReferenceEngine):
    """WRONG engine: the per-loop heads are assigned to the wrong loops
    (readout reads loop T+1-t's head at loop t). P1-4 detector."""

    name = "swapped-readout"

    def conf_at(self, t: int) -> int:
        h = self.h0
        for _ in range(t):
            h = _step(h)
        return max(_read(SPEC_T + 1 - t, h), 100 - _read(SPEC_T + 1 - t, h))


class UngatedEngine(ReferenceEngine):
    """basal 2.8.1 class: max_error silently ignored outside act/tool."""

    name = "ungated"

    def gate(self, conf: int, tau: int, qtype: str = "choice") -> str:
        if qtype in GATED_TYPES:
            return "argmax" if conf >= tau else "none"
        return "argmax"  # decides regardless — the violation


def gate_calib(calib: dict | None, qtype: str, t: int, conf: int) -> str:
    """Mirror of gateCalib (Loop.lean): a calibration applies only at its
    own question type and loop index; otherwise no decision. `None` is
    the mirror of `gateOptCalib none` (no calibration record at all)."""
    if calib is None:
        return "none"
    if calib["qtype"] == qtype and calib["loopIdx"] == t:
        return _gate_p(calib["tau"], conf)
    return "none"


def gate_loop(calib: dict | None, lr: dict) -> str:
    """Mirror of gateLoop (Loop.lean): the index comes from the RESPONSE
    itself (lr = {qtype, loopIdx, conf}), not from a caller argument."""
    return gate_calib(calib, lr["qtype"], lr["loopIdx"], lr["conf"])


def test_vector_integrity() -> None:
    assert V["h0"] == encode_once(V["state"]), "h0 must be encode-once of the state"
    assert PIN["T"] == SPEC_T, "frozen budget must equal the pinned spec_T"
    for key in ("conf_trace", "probs_trace", "gate_tau75", "is_hard_K2",
                "reinjected_raw_trace"):
        assert len(V[key]) == SPEC_T, f"{key} aligned with budgets 1..T"
    # every trace entry is the confidence of a constructed binary response
    for probs, conf in zip(V["probs_trace"], V["conf_trace"]):
        assert len(probs) == 2 and sum(probs) == 100, f"probs not a normalized binary response: {probs}"
        assert conf == max(probs), f"conf != max(probs) for {probs}"
        assert 50 <= conf <= 100, f"conf outside the binary response range: {conf}"


def test_encode_matches_frozen() -> None:
    """encode is Python-only (sha256 not in Lean core): assert against the
    frozen h0 — documented boundary of the three-way check."""
    assert encode_once(V["state"]) == V["h0"]


def _gate_calib_cases() -> list:
    """The Python mirror of the six exported gateCalib cases, computed
    from the pin and the frozen conf trace:
      1. calib(loop 3, τ₀) @ loop 3   — applicable, below τ₀
      2. calib(loop 3, τ₀) @ loop 8   — wrong loop
      3. calib(loop 3, τ₀) @ act 3    — wrong question type
      4. none        @ loop 3         — no calibration record
      5. calib(loop 5, τ₀-1) @ loop 5 — applicable, ABOVE τ₀-1: DECIDES
      6. calib(loop 3, conf8-1) @ loop 8 — wrong loop, τ WOULD decide
    """
    tau0 = CALIBRATION_THRESHOLD
    tau1 = tau0 - 1
    conf8 = V["conf_trace"][SPEC_T - 1]
    calib3 = {"qtype": "choice", "loopIdx": 3, "tau": tau0}
    calib5 = {"qtype": "choice", "loopIdx": 5, "tau": tau1}
    calibD = {"qtype": "choice", "loopIdx": 3, "tau": conf8 - 1}
    conf3 = V["conf_trace"][2]
    conf5 = V["conf_trace"][4]
    return [
        gate_calib(calib3, "choice", 3, conf3),   # own loop, per threshold
        gate_calib(calib3, "choice", 8, conf8),   # wrong loop
        gate_calib(calib3, "act", 3, conf3),      # wrong question type
        "none",                                   # no calibration at all
        gate_calib(calib5, "choice", 5, conf5),   # own loop, DECIDING
        gate_calib(calibD, "choice", 8, conf8),   # wrong loop, τ would decide
    ]


def test_lean_export_matches_frozen() -> None:
    """The proved definitions, executed, must reproduce the frozen vectors
    — including the full distributions and the calibration cases."""
    lean = lean_export()
    assert lean["conf_trace"] == V["conf_trace"], "Lean trace != frozen trace"
    assert lean["reinjected_raw_trace"] == V["reinjected_raw_trace"], (
        "Lean reinjected (raw) trace != frozen"
    )
    assert lean["is_hard_K2"] == V["is_hard_K2"], "Lean isHard != frozen"
    assert lean["gate_tau"] == V["gate_tau75"], "Lean gate != frozen gate"
    assert lean["probs_trace"] == V["probs_trace"], "Lean probs != frozen probs"
    assert lean["gate_calib_cases"] == V["gate_calib_cases"], (
        "Lean gateCalib cases != frozen"
    )
    assert lean["loop_response_wrong_loop"] == V["loop_response_wrong_loop"], (
        "Lean LoopResponse case != frozen"
    )
    # score fields — the FULL three-way bridge for the score contract
    assert lean["score_value"] == V["score_value"], "Lean score value != frozen"
    assert lean["score_conf"] == V["score_conf"], "Lean score conf != frozen"
    assert lean["score_conf_loop"] == V["score_conf_loop"], (
        "Lean score conf loop != frozen"
    )
    assert lean["score_gate"] == V["score_gate"], "Lean score gate != frozen"
    assert lean["score_payload_positive"] == V["score_payload_positive"], (
        "Lean score payload positive != frozen"
    )
    assert lean["score_gate_positive"] == V["score_gate_positive"], (
        "Lean score gate positive != frozen"
    )
    assert lean["score_gate_wrong_loop"] == V["score_gate_wrong_loop"], (
        "Lean score gate wrong loop != frozen"
    )
    assert lean["score_gate_updated"] == V["score_gate_updated"], (
        "Lean score gate updated != frozen"
    )
    assert lean["score_ev"] == V["score_ev"], "Lean score EV != frozen"
    assert lean["score_exact_num"] == V["score_exact_num"], (
        "Lean score exact numerator != frozen"
    )
    # the exported probs are the response's own (binResponseOf_probs twin)
    for probs, conf in zip(lean["probs_trace"], lean["conf_trace"]):
        assert conf == max(probs), "Lean: conf != max(probs)"


def test_probs_trace_three_way() -> None:
    """Three independent computations of the distributions must agree:
    Python computes them from ITS OWN readout (not from the frozen file),
    Lean from the constructed Response, and the frozen vectors carry the
    pin. conf == max(probs) closes the Response contract on all layers."""
    ref = ReferenceEngine(V["state"])
    got = [ref.probs_at(t) for t in range(1, SPEC_T + 1)]
    assert got == V["probs_trace"], (
        f"Python probs != frozen: {got} != {V['probs_trace']}"
    )
    for probs, conf in zip(V["probs_trace"], V["conf_trace"]):
        assert len(probs) == 2 and sum(probs) == 100
        assert conf == max(probs), "frozen: conf != max(probs)"


def test_gate_calib_three_way() -> None:
    """frozen == Python == (Lean in test_lean_export_matches_frozen): the
    four calibration cases agree across all three layers."""
    assert _gate_calib_cases() == V["gate_calib_cases"], (
        "Python gateCalib cases != frozen"
    )
    # per-case semantics, independent of the frozen file:
    tau0 = CALIBRATION_THRESHOLD
    tau1 = tau0 - 1
    calib3 = {"qtype": "choice", "loopIdx": 3, "tau": tau0}
    calib5 = {"qtype": "choice", "loopIdx": 5, "tau": tau1}
    conf3 = V["conf_trace"][2]
    conf5 = V["conf_trace"][4]
    conf8 = V["conf_trace"][SPEC_T - 1]
    # own loop: the threshold rule decides (below tau here -> none)
    assert gate_calib(calib3, "choice", 3, conf3) == (
        "argmax" if tau0 <= conf3 else "none"
    )
    # wrong loop: the calibration does not apply, regardless of threshold
    # (twin of wrong_loop_never_decides — holds for ANY tau)
    assert gate_calib(calib3, "choice", 8, conf8) == "none"
    # wrong question type: no decision, even at conf 100
    assert gate_calib(calib3, "noul", 3, 100) == "none"
    # no calibration record: no decision (twin of no_calib_never_decides)
    assert gate_calib(None, "choice", 3, 100) == "none"
    # POSITIVE path: own loop at tau0-1 with conf5 above it — the full
    # gateCalib chain (applicability AND threshold) produces a decision
    assert tau1 < conf5, "test setup: tau1 must decide at loop 5"
    assert gate_calib(calib5, "choice", 5, conf5) == "argmax"
    # WRONG-LOOP REGRESSION with an index-isolating threshold: tau2 =
    # conf8 - 1 WOULD decide at loop 8 were the index ignored; the
    # correct implementation returns none (mirror of wrong_loop_structural)
    calibD = {"qtype": "choice", "loopIdx": 3, "tau": conf8 - 1}
    assert _gate_p(conf8 - 1, conf8) == "argmax", (
        "test setup: tau2 must decide at loop 8 absent the index check"
    )
    assert gate_calib(calibD, "choice", 8, conf8) == "none", (
        "wrong loop must defer even when the threshold would decide"
    )


def test_loop_response_binding() -> None:
    """The LoopResponse mirror: the index travels with the response, so a
    loop-3 calibration cannot decide on a loop-8 response — the structural
    twin of wrong_loop_structural, compared with the Lean export too.
    The threshold here (conf8 - 1) WOULD decide at loop 8, isolating the
    index check: a gateLoop that ignored lr.loopIdx would return argmax."""
    tau2 = V["conf_trace"][SPEC_T - 1] - 1
    calibD = {"qtype": "choice", "loopIdx": 3, "tau": tau2}
    lr8 = {"qtype": "choice", "loopIdx": 8, "conf": V["conf_trace"][SPEC_T - 1]}
    assert _gate_p(tau2, lr8["conf"]) == "argmax", (
        "test setup: the threshold would decide at loop 8 absent the index"
    )
    assert gate_loop(calibD, lr8) == "none", (
        "gateLoop must read the index from the response: loop-3 calib vs loop-8 response"
    )
    # honest call site: gateLoop == gateCalib (twin of gateLoop_eq_gateCalib)
    lr3 = {"qtype": "choice", "loopIdx": 3, "conf": V["conf_trace"][2]}
    assert gate_loop(calibD, lr3) == gate_calib(
        calibD, "choice", 3, V["conf_trace"][2]
    ), "gateLoop must agree with gateCalib at honest call sites"

    # MUTATION TEST: a gate that ignores the loop index must FAIL this suite
    # (this is exactly the bug class wrong_loop_structural rules out).
    def gate_loop_ignoring_index(calib, lr):
        if calib is None:
            return "none"
        return _gate_p(calib["tau"], lr["conf"])  # lr.loopIdx never consulted

    assert gate_loop_ignoring_index(calibD, lr8) == "argmax", (
        "test setup: the index-ignoring mutation MUST be detectable — "
        "if this assert fails, the wrong-loop case no longer isolates the bug"
    )


# ---- multi-label conformance (v1.4.2) ----

def _mirror_gate_multi(tau, labels, confs):
    """Python mirror of gateMulti: per-label gate from each label's own
    confidence, label order preserved."""
    return labels, [_gate_p(tau, c) for c in confs]


def test_multi_golden() -> None:
    """The Lean-exported multi collection: 3 labels, different per-label
    distributions, mixed gating at the calibration threshold."""
    labels = V["multi_labels"]
    confs = V["multi_conf_trace"]
    assert labels == ["alpha", "beta", "gamma"], "label order must be preserved"
    assert len(confs) == len(labels) == 3, "three labels, three decisions"
    assert len(V["multi_probs_trace"]) == 3, "one distribution per label"
    for probs, conf in zip(V["multi_probs_trace"], confs):
        assert len(probs) == 2 and sum(probs) == 100
        assert conf == max(probs), "per-label conf != max(per-label probs)"
        assert 50 <= conf <= 100, "per-label conf outside the binary range"
    # mixed gating: the frozen gates are the Python mirror of the SAME rule
    _, mirrored = _mirror_gate_multi(CALIBRATION_THRESHOLD, labels, confs)
    assert mirrored == V["multi_gate_tau"], (
        f"Python gateMulti != frozen: {mirrored} != {V['multi_gate_tau']}"
    )
    # and the collection genuinely MIXES outcomes (the case is discriminating)
    assert len(set(V["multi_gate_tau"])) == 2, (
        "frozen multi gating must mix argmax and none"
    )


def test_multi_update_locality() -> None:
    """Updating label 2 (index 1) with the loop-4 readout changes ONLY
    position 2 — positions 1 and 3 keep their gated outcomes (the Python
    mirror of gateMulti_set_independent / multi_set_independent). The
    expected result is computed INDEPENDENTLY from the engine: the update
    is the loop-4 readout gated at the calibration threshold."""
    before = V["multi_gate_tau"]
    after = V["multi_gate_tau_updated"]
    labels_u = V["multi_labels_updated"]
    assert labels_u == V["multi_labels"], "update must not touch the label list"
    assert len(after) == len(before) == 3
    assert after[0] == before[0] and after[2] == before[2], (
        "positions 1 and 3 must be unchanged by the label-2 update"
    )
    # the update is VISIBLE at position 2 — not a no-op
    assert before[1] != after[1], (
        "position 2 must CHANGE under the label-2 update (loop-4 readout)"
    )
    # INDEPENDENT expectation: before.copy with position 2 = gate at the
    # loop-4 readout's confidence
    ref = ReferenceEngine(V["state"])
    expected = before.copy()
    expected[1] = _gate_p(CALIBRATION_THRESHOLD, ref.conf_at(4))
    assert after == expected, (
        f"after != independently computed: {after} != {expected}"
    )
    # and the expected value genuinely differs from `before` at position 2
    # (loop-4 conf 72 < tau=75 => none, vs before's argmax) — the data is
    # discriminating
    assert _gate_p(CALIBRATION_THRESHOLD, ref.conf_at(4)) != before[1], (
        "test setup: the loop-4 readout must gate DIFFERENTLY than label 2's original"
    )
    # the updated label-2 confidence is the loop-2 readout's (before update)
    assert V["multi_conf_trace"][1] == ref.conf_at(2), (
        "label 2's original conf must be the loop-2 readout"
    )
    # and the mirrored per-label confs reproduce the frozen ones exactly
    mirrored_confs = [ref.conf_at(i + 1) for i in range(3)]
    assert mirrored_confs == V["multi_conf_trace"], (
        "Python per-label confs != frozen"
    )
    # full per-label distributions get their independent check too
    mirrored_probs = [ref.probs_at(i + 1) for i in range(3)]
    assert mirrored_probs == V["multi_probs_trace"], (
        "Python per-label probs != frozen"
    )
    # the updated gate is compared field-by-field with the mirror
    # (scoreOfDist: EV=54, conf from loop 5, calib at loop 5, 54 < 75)
    assert V["score_gate_updated"] == "none"


def test_multi_rejects() -> None:
    """Negative cases: duplicate labels and out-of-range update index are
    REJECTED by the well-formedness conditions (Python mirrors of
    labels_nodup and the Fin index)."""
    labels = V["multi_labels"]
    # duplicate labels: Nodup fails
    dup = [labels[0], labels[0], labels[1]]
    assert len(dup) == 3 and dup.count(dup[0]) == 2, "test setup: dup has a duplicate"
    # the mirror's well-formedness check (mirror of labels_nodup)
    def well_formed(labels_, decisions):
        return len(labels_) == len(decisions) and len(set(labels_)) == len(labels_)
    assert not well_formed(dup, [0, 0, 0]), "duplicates must be rejected"
    assert well_formed(labels, [0, 0, 0]), "the frozen collection is well-formed"
    # out-of-range index: Fin m.labels.length rejects index 3 for 3 labels
    def valid_index(i, labels_):
        return 0 <= i < len(labels_)
    assert not valid_index(3, labels), "index 3 must be rejected for 3 labels"
    assert valid_index(1, labels), "index 1 is in range"


# ---- score conformance (v1.5, hardened v1.5.1) ----

def _mirror_gate_score(calib_loop, conf_loop, conf, value):
    """Python mirror of gateScore: the payload is the VALUE (never the
    confidence); below the threshold or at a wrong loop the gate abstains.
    Bounds are VALIDATED on the whole [0,100] scale (a response with
    value or conf > 100 or < 0 is ill-formed — mirror of the structure's
    `value_le_100`/`conf_le_100` over Nat; non-integer input is a type
    error by itself)."""
    if not (isinstance(value, int) and isinstance(conf, int)):
        raise TypeError("score fields must be integers (Nat)")
    if not 0 <= value <= 100 or not 0 <= conf <= 100:
        raise ValueError("ill-formed score response: value/confidence off the [0,100] scale")
    if calib_loop != conf_loop:
        return None
    return value if tau_le(conf, calib_tau) else None


def tau_le(conf, tau):
    """Mirror of gateP: tau <= conf."""
    return tau <= conf

# the calibration object for the mirrors (bound to loop 5, tau = the pin's
# calibration threshold) — mirrors ScoreCalib { tau, threshold_le_100, loopIdx }
calib_tau = CALIBRATION_THRESHOLD


def test_score_golden() -> None:
    """The Lean-exported score response: value and confidence come from
    DIFFERENT loops (separate quantities made visible in the data), the
    gate at the calibration threshold mirrors the rule in ALL branches
    (none / payload=value / wrong-loop), and the demo expected value is
    54 with exact numerator 5400."""
    ref = ReferenceEngine(V["state"])
    # value = loop-2 raw readout, confidence = loop-5 raw readout
    assert V["score_value"] == ref.raw_at(2), "score value must be the loop-2 readout"
    assert V["score_conf"] == ref.raw_at(5), "score conf must be the loop-5 readout"
    assert V["score_conf_loop"] == 5, "the exported confidence carries its loop"
    # the export demonstrates the separation: value != confidence
    assert V["score_value"] != V["score_conf"], (
        "the exported score response must have value != confidence"
    )
    # gating mirrors gateScore in ALL THREE branches:
    # 1. abstention (loop 5 matches, conf 20 < 75)
    assert V["score_gate"] == "none", "score gate must defer below the threshold"
    assert _mirror_gate_score(5, 5, V["score_conf"], V["score_value"]) is None
    # 2. positive path (loop 2 matches, conf 84 >= 75): payload = value 52
    assert V["score_gate_positive"] == "argmax", "positive path must decide"
    assert V["score_payload_positive"] == ref.raw_at(6), (
        "the payload must be the VALUE (loop-6 readout), not the confidence"
    )
    assert V["score_payload_positive"] != V["score_conf"], (
        "payload must not be the confidence (84)"
    )
    assert _mirror_gate_score(2, 2, 84, ref.raw_at(6)) == V["score_payload_positive"], (
        "Python mirror of the positive path must equal the frozen payload"
    )
    # 3. wrong loop (calib at 5, conf from 2): none even though 84 >= 75
    assert V["score_gate_wrong_loop"] == "none", "wrong loop must abstain"
    assert _mirror_gate_score(5, 2, 84, ref.raw_at(6)) is None
    # expected value of the demo distribution: floor of exact EV
    dist = [(30, 40), (70, 60)]
    assert sum(v * w for v, w in dist) // 100 == V["score_ev"] == 54
    assert sum(v * w for v, w in dist) == V["score_exact_num"] == 5400


def test_score_rejects() -> None:
    """Negative and boundary cases (Python mirrors of the score contract's
    theorems): below threshold the gate abstains (gateScore_defers_below);
    the deciding payload is the VALUE, never the confidence
    (gateScore_payload_is_value); wrong loop abstains regardless
    (gateScore_wrong_loop_never_decides); ill-formed responses (value or
    confidence off the [0,100] scale) are REJECTED by validation."""
    tau = CALIBRATION_THRESHOLD
    # deferral below threshold — even for a large value
    assert _mirror_gate_score(5, 5, tau - 1, 99) is None
    # deciding payload is the value, NOT the confidence
    assert _mirror_gate_score(2, 2, tau, 85) == 85
    assert _mirror_gate_score(2, 2, 100, 30) == 30
    # wrong loop abstains regardless of the confidence
    assert _mirror_gate_score(5, 2, tau, 85) is None
    assert _mirror_gate_score(5, 2, 100, 30) is None
    # updated path (scoreOfDist: EV=54 of the demo dist, conf from loop 5,
    # loop 5 matches, 54 < 75 ⇒ none) — compared with the frozen field
    assert V["score_gate_updated"] == "none"
    assert _mirror_gate_score(5, 5, 54, 54) is None
    # ILL-FORMED responses are rejected (validation, not silent acceptance):
    # value/conf > 100 or < 0 are off the scale — mirror of
    # value_le_100 / conf_le_100 over Nat
    for bad in ((5, 5, 101, 20), (5, 5, 20, 101), (5, 5, -1, 20), (5, 5, 20, -1)):
        calib_loop, conf_loop, value, conf = bad
        try:
            _mirror_gate_score(calib_loop, conf_loop, conf, value)
            raise AssertionError(f"ill-formed response must be rejected: {bad}")
        except ValueError:
            pass
    # bounds: raw readouts stay ≤ 100 by construction
    ref = ReferenceEngine(V["state"])
    for t in range(1, SPEC_T + 1):
        assert ref.raw_at(t) <= 100


def test_reference_matches_frozen_trace() -> None:
    ref = ReferenceEngine(V["state"])
    got = [ref.conf_at(t) for t in range(1, SPEC_T + 1)]
    assert got == V["conf_trace"], f"reference trace diverges: {got} != {V['conf_trace']}"


def test_ishard_matches_frozen_and_boundary() -> None:
    """The Python mirror of isHard must reproduce the frozen vector AND
    the pinned boundary (75 decides, 74 does not)."""
    assert [_is_hard(2, c) for c in V["conf_trace"]] == V["is_hard_K2"], (
        "Python isHard != frozen is_hard_K2"
    )
    assert _is_hard(2, HARD_ANSWER_THRESHOLD_K2 - 1) is False
    assert _is_hard(2, HARD_ANSWER_THRESHOLD_K2) is True


def test_gate_matches_frozen_and_boundary() -> None:
    """gateP mirror: frozen gate vector, boundary at tau-1/tau, and every
    question type gates identically in the conforming policy."""
    assert [_gate_p(CALIBRATION_THRESHOLD, c) for c in V["conf_trace"]] == V["gate_tau75"], (
        "Python gateP != frozen gate_tau75"
    )
    for qtype in ("act", "tool", "choice", "noul", "score", "multi"):
        assert ReferenceEngine(V["state"]).gate(
            CALIBRATION_THRESHOLD - 1, CALIBRATION_THRESHOLD, qtype
        ) == "none", f"gate must defer at tau-1 ({qtype})"
        assert ReferenceEngine(V["state"]).gate(
            CALIBRATION_THRESHOLD, CALIBRATION_THRESHOLD, qtype
        ) == "argmax", f"gate must decide at tau ({qtype})"


def test_reinjected_engine_fails_suite() -> None:
    """The divergence must be real AND measured on the same quantity:
    raw readout vs raw readout (both engines' `raw_at`), mirroring Lean's
    `reinjection_differs` (which compares the raw `read` values). The
    reinjected raw trace matches its own frozen trace, which is the RAW
    scalar per loop — not the response confidence."""
    eng = ReinjectedEngine(V["state"])
    ref = ReferenceEngine(V["state"])
    got_raw = [eng.raw_at(t) for t in range(1, SPEC_T + 1)]
    ref_raw = [ref.raw_at(t) for t in range(1, SPEC_T + 1)]
    assert got_raw == V["reinjected_raw_trace"], (
        "reinjected engine must match its own frozen (raw) trace"
    )
    assert got_raw != ref_raw, "raw-vs-raw: reinjection was NOT detected"
    # and the same holds after constructing responses (conf = f(raw))
    assert [max(r, 100 - r) for r in got_raw] != V["conf_trace"], (
        "confidence-vs-confidence: reinjection was NOT detected"
    )


def test_swapped_readout_diverges() -> None:
    """Per-loop readouts matter: assigning heads to the wrong loops must
    diverge from the reference trace (P1-4)."""
    ref = ReferenceEngine(V["state"])
    swapped = SwappedReadoutEngine(V["state"])
    got = [swapped.conf_at(t) for t in range(1, SPEC_T + 1)]
    want = [ref.conf_at(t) for t in range(1, SPEC_T + 1)]
    assert got != want, "swapped per-loop readout was NOT detected"


def test_calibration_loop_binding() -> None:
    """A calibration fitted at loop 3 must not gate loop 8 — even when its
    threshold WOULD decide there (twin of wrong_loop_never_decides)."""
    conf8 = V["conf_trace"][SPEC_T - 1]
    tau = conf8 - 1  # strictly below the loop-8 confidence: would decide there
    assert 0 <= tau and tau <= conf8, "test setup: tau must decide at loop 8"
    calib3 = {"qtype": "choice", "loopIdx": 3, "tau": tau}
    assert gate_calib(calib3, "choice", 8, conf8) == "none", (
        "calibration from loop 3 must not decide at loop 8"
    )
    conf3 = V["conf_trace"][2]
    assert gate_calib(calib3, "choice", 3, conf3) == (
        "argmax" if tau <= conf3 else "none"
    ), "calibration must apply at its own loop"
    # wrong question type: also no decision
    calib_choice = {"qtype": "choice", "loopIdx": 3, "tau": tau}
    assert gate_calib(calib_choice, "noul", 3, 100) == "none", (
        "calibration must not apply to another question type"
    )


def test_ungated_engine_violates_conformance() -> None:
    """Below threshold, a conforming gate returns 'none' for every type;
    the ungated engine decides anyway for choice/noul/score/multi —
    the reported 2.8.1 finding class, reproduced for each type."""
    ungated = UngatedEngine(V["state"])
    ref = ReferenceEngine(V["state"])
    below = [c for c in V["conf_trace"] if c < CALIBRATION_THRESHOLD]
    assert below, "vectors must contain below-threshold cases"
    for qtype in AFFECTED_TYPES:
        for c in below:
            assert ungated.gate(c, CALIBRATION_THRESHOLD, qtype) == "argmax", (
                f"ungated engine must violate for {qtype} at conf={c}"
            )
            assert ref.gate(c, CALIBRATION_THRESHOLD, qtype) == "none", (
                f"reference gate must defer for {qtype} at conf={c}"
            )
    # act/tool stay gated even in the buggy policy
    for qtype in GATED_TYPES:
        for c in below:
            assert ungated.gate(c, CALIBRATION_THRESHOLD, qtype) == "none", (
                f"act/tool must stay gated even in the selective policy ({qtype})"
            )


def main() -> int:
    parser = argparse.ArgumentParser(description="three-way conformance suite")
    parser.add_argument("--fast", action="store_true",
                        help="skip the Lean export (no lake needed)")
    parser.add_argument("--only", type=str, default=None,
                        help="run only tests whose name contains this substring")
    args = parser.parse_args()

    tests = [
        test_vector_integrity,
        test_encode_matches_frozen,
        test_lean_export_matches_frozen,
        test_probs_trace_three_way,
        test_gate_calib_three_way,
        test_loop_response_binding,
        test_multi_golden,
        test_multi_update_locality,
        test_multi_rejects,
        test_score_golden,
        test_score_rejects,
        test_reference_matches_frozen_trace,
        test_ishard_matches_frozen_and_boundary,
        test_gate_matches_frozen_and_boundary,
        test_reinjected_engine_fails_suite,
        test_swapped_readout_diverges,
        test_calibration_loop_binding,
        test_ungated_engine_violates_conformance,
    ]
    if args.only:
        tests = [t for t in tests if args.only in t.__name__]
        if not tests:
            print(f"--only {args.only!r}: no test matches", file=sys.stderr)
            return 2
    if args.fast:
        tests = [t for t in tests if t is not test_lean_export_matches_frozen]

    failures = 0
    for t in tests:
        try:
            t()
            print(f"PASS {t.__name__}")
        except AssertionError as e:
            failures += 1
            print(f"FAIL {t.__name__}: {e}")
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main())
