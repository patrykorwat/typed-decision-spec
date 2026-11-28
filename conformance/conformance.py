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

sys.path.insert(0, str(Path(__file__).resolve().parent))
import adapter  # Phase B/B2 reference adapter (issue #19)

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
    assert lean["score_gate_boundary"] == V["score_gate_boundary"], (
        "Lean score gate boundary != frozen"
    )
    assert lean["score_ev"] == V["score_ev"], "Lean score EV != frozen"
    assert lean["score_exact_num"] == V["score_exact_num"], (
        "Lean score exact numerator != frozen"
    )
    # act fields — the FULL three-way bridge for the act contract
    assert lean["act_actions"] == V["act_actions"], "Lean act actions != frozen"
    assert lean["act_cost_nums"] == V["act_cost_nums"], (
        "Lean act cost numerators != frozen"
    )
    assert lean["act_selected"] == V["act_selected"], "Lean act selected != frozen"
    assert lean["act_conf"] == V["act_conf"], "Lean act conf != frozen"
    assert lean["act_conf_loop"] == V["act_conf_loop"], "Lean act conf loop != frozen"
    assert lean["act_gate"] == V["act_gate"], "Lean act gate != frozen"
    assert lean["act_gate_payload"] == V["act_gate_payload"], (
        "Lean act gate payload != frozen"
    )
    assert lean["act_gate_positive"] == V["act_gate_positive"], (
        "Lean act gate positive != frozen"
    )
    assert lean["act_gate_payload_positive"] == V["act_gate_payload_positive"], (
        "Lean act gate payload positive != frozen"
    )
    # the SCALE BOUNDARY case (τ = 100, constructed conf = 100) — same bridge
    assert lean["act_gate_boundary"] == V["act_gate_boundary"], (
        "Lean act gate boundary != frozen"
    )
    assert lean["act_gate_payload_boundary"] == V["act_gate_payload_boundary"], (
        "Lean act gate payload boundary != frozen"
    )
    # the TIE-BREAK vector — computed fields through the same bridge
    assert lean["act_tie_actions"] == V["act_tie_actions"], (
        "Lean act tie actions != frozen"
    )
    assert lean["act_tie_cost_nums"] == V["act_tie_cost_nums"], (
        "Lean act tie cost numerators != frozen"
    )
    assert lean["act_tie_selected"] == V["act_tie_selected"], (
        "Lean act tie selected != frozen"
    )
    assert lean["act_tie_gate_positive"] == V["act_tie_gate_positive"], (
        "Lean act tie gate positive != frozen"
    )
    assert lean["act_tie_gate_payload_positive"] == V["act_tie_gate_payload_positive"], (
        "Lean act tie gate payload positive != frozen"
    )
    # the TOOL contract — the FULL three-way bridge (all 10 fields)
    assert lean["tool_tools"] == V["tool_tools"], "Lean tool tools != frozen"
    assert lean["tool_selected"] == V["tool_selected"], "Lean tool selected != frozen"
    assert lean["tool_conf"] == V["tool_conf"], "Lean tool conf != frozen"
    assert lean["tool_conf_loop"] == V["tool_conf_loop"], (
        "Lean tool conf loop != frozen"
    )
    assert lean["tool_gate"] == V["tool_gate"], "Lean tool gate != frozen"
    assert lean["tool_gate_payload"] == V["tool_gate_payload"], (
        "Lean tool gate payload != frozen"
    )
    assert lean["tool_gate_positive"] == V["tool_gate_positive"], (
        "Lean tool gate positive != frozen"
    )
    assert lean["tool_gate_payload_positive"] == V["tool_gate_payload_positive"], (
        "Lean tool gate payload positive != frozen"
    )
    # the WRONG-LOOP vectors — computed fields through the same bridge
    # (calib at loop 5, the response's confidence from loop 2, 84 >= tau)
    assert lean["act_gate_wrong_loop"] == V["act_gate_wrong_loop"], (
        "Lean act gate wrong loop != frozen"
    )
    assert lean["tool_gate_wrong_loop"] == V["tool_gate_wrong_loop"], (
        "Lean tool gate wrong loop != frozen"
    )
    assert lean["tool_gate_boundary"] == V["tool_gate_boundary"], (
        "Lean tool gate boundary != frozen"
    )
    assert lean["tool_gate_payload_boundary"] == V["tool_gate_payload_boundary"], (
        "Lean tool gate payload boundary != frozen"
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
    assert V["score_gate_updated"] is None


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
    Fields must be STRICT integers (`type(x) is int` — bool is a subclass
    of int in Python and is NOT accepted, mirror of Nat), validated on
    the whole [0,100] scale in both directions; loop indices must be
    integers too."""
    if type(value) is not int or type(conf) is not int:
        raise TypeError("score fields must be integers (Nat)")
    if type(calib_loop) is not int or type(conf_loop) is not int:
        raise TypeError("loop indices must be integers (Nat)")
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
    # 4. scale boundary (τ = 100 with constructed conf = 100): decides —
    # the exported conf = None (abstention) case stays a real abstention
    assert V["score_gate_boundary"] == "argmax", "boundary τ=100 must decide"
    assert V["score_gate_updated"] is None
    assert _mirror_gate_score(2, 2, 100, ref.raw_at(6)) == V["score_payload_positive"]
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
    # loop 5 matches, 54 < 75 ⇒ null) — compared with the frozen field
    assert V["score_gate_updated"] is None
    assert _mirror_gate_score(5, 5, 54, 54) is None
    # TYPE rejections (TypeError — strict int, bool is NOT accepted):
    # bool fields, float fields, string fields, and non-integer loop indices
    for bad in ((5, 5, True, False), (5, 5, 85.0, 55), (5, 5, "85", 55),
                (5.0, 5, 85, 55), (5, True, 85, 55)):
        calib_loop, conf_loop, value, conf = bad
        try:
            _mirror_gate_score(calib_loop, conf_loop, conf, value)
            raise AssertionError(f"non-integer field must raise TypeError: {bad}")
        except TypeError:
            pass
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


# ---- act conformance (v1.6) ----

def _mirror_gate_act(calib_loop, conf_loop, conf, selected):
    """Python mirror of gateAct: the payload is the SELECTED ACTION
    (never a cost, never the confidence); below the threshold or at a
    wrong loop the gate abstains. Confidence validated on the [0,100]
    scale (mirror of `conf_le_100`; the calibration's own bound is
    `threshold_le_100`), and strict-integer fields (mirror of Nat —
    negative loop indices are NOT silently accepted)."""
    if not (isinstance(selected, str) and type(conf) is int
            and type(calib_loop) is int and type(conf_loop) is int):
        raise TypeError("act fields must be (str, int, int, int)")
    if not 0 <= conf <= 100:
        raise ValueError("ill-formed act response: confidence off the [0,100] scale")
    if calib_loop < 0 or conf_loop < 0:
        raise ValueError("ill-formed act response: negative loop index (mirror of Nat)")
    if calib_loop != conf_loop:
        return None
    return selected if tau_le(conf, calib_tau) else None


def test_act_golden() -> None:
    """The Lean-exported act collection: 3 actions with different cost
    distributions (exact numerators 1000/3000/2000), selection by
    MINIMUM exact cost computed INDEPENDENTLY from the numerators list,
    the gate at the calibration threshold in ALL branches, and the
    payload being the ACTION identifier."""
    actions = V["act_actions"]
    assert actions == ["deploy", "rollback", "wait"], "label order must be preserved"
    nums = V["act_cost_nums"]
    assert nums == [1000, 3000, 2000], "exact cost numerators computed per action"
    # INDEPENDENT minimum: index of the smallest numerator
    min_idx = nums.index(min(nums))
    assert V["act_selected"] == actions[min_idx], (
        "the selected action must be the one at the minimum-exact-cost position"
    )
    assert V["act_selected"] == "deploy" == actions[0], (
        "the minimum-exact-cost action must be selected (deploy, 1000)"
    )
    # TIE-BREAK: with EQUAL numerators the FIRST-declared action wins;
    # index() returns the FIRST minimum — the first-declared rule,
    # derived independently from the exported tie numerators
    tie_actions = V["act_tie_actions"]
    tie_nums = V["act_tie_cost_nums"]
    assert tie_actions == ["rollback", "wait"], "the tie case must have two actions"
    assert tie_nums == [3000, 3000], "the tie case must tie on the exact numerator"
    assert V["act_tie_selected"] == tie_actions[tie_nums.index(min(tie_nums))], (
        "with equal numerators the FIRST-declared action must be selected"
    )
    assert V["act_tie_selected"] == "rollback", "rollback (declared first) wins the tie"
    # positive path: calib bound to loop 2, confidence from loop 2 (84 >= 75)
    assert V["act_gate_positive"] == "decided", "positive path must decide"
    assert V["act_gate_payload_positive"] == "deploy", (
        "the payload must be the ACTION identifier, not a cost and not the confidence"
    )
    # the deciding gate on the TIED response returns the SELECTED ACTION
    assert V["act_tie_gate_positive"] == "decided", "the tie gate must decide (84 >= tau)"
    assert V["act_tie_gate_payload_positive"] == "rollback", (
        "the tie payload must be the SELECTED (first-declared) action"
    )
    assert _mirror_gate_act(2, 2, 84, "rollback") == "rollback"
    # the mirror agrees on the positive path
    assert _mirror_gate_act(2, 2, 84, "deploy") == "deploy"
    # the SCALE BOUNDARY case: τ = 100 with the constructed conf AT 100 —
    # decides; payload is the selected action (mirror agrees)
    assert V["act_gate_boundary"] == "decided", "boundary τ=100 must decide"
    assert V["act_gate_payload_boundary"] == "deploy"
    assert _mirror_gate_act(2, 2, 100, "deploy") == "deploy"
    # abstention: calib at loop 5, conf 20 < 75
    assert V["act_gate"] == "none", "act gate must defer below the threshold"
    assert _mirror_gate_act(5, 5, 20, "deploy") is None
    # wrong loop: calib at 5, conf from loop 2 — abstains despite 84 >= 75
    # (the frozen field exercises the same case through the bridge)
    assert V["act_gate_wrong_loop"] == "none", "wrong loop must abstain (frozen)"
    assert _mirror_gate_act(5, 2, 84, "deploy") is None


def test_act_rejects() -> None:
    """Negative and boundary cases (Python mirrors of the act contract's
    theorems): below threshold the gate abstains (gateAct_defers_below);
    the deciding payload is the ACTION, never a cost or the confidence
    (gateAct_payload_is_action); wrong loop abstains
    (gateAct_wrong_loop_never_decides); ill-formed responses —
    non-integer fields, confidence off the scale, negative loop
    indices, non-string action —
    are REJECTED by validation."""
    tau = CALIBRATION_THRESHOLD
    # deferral below threshold — even for an attractive action
    assert _mirror_gate_act(5, 5, tau - 1, "deploy") is None
    # deciding payload is the action, NOT a cost and NOT the confidence
    assert _mirror_gate_act(2, 2, tau, "deploy") == "deploy"
    assert _mirror_gate_act(2, 2, 100, "rollback") == "rollback"
    # wrong loop abstains regardless of the confidence
    assert _mirror_gate_act(5, 2, tau, "deploy") is None
    assert _mirror_gate_act(5, 2, 100, "wait") is None
    # TYPE rejections: non-integer confidence, non-integer loop indices
    for bad in ((5, 5, 85.0, "deploy"), (5, True, 85, "deploy")):
        calib_loop, conf_loop, conf, selected = bad
        try:
            _mirror_gate_act(calib_loop, conf_loop, conf, selected)
            raise AssertionError(f"non-integer field must raise TypeError: {bad}")
        except TypeError:
            pass
    # ILL-FORMED: confidence off the scale
    for bad in ((5, 5, 101, "deploy"), (5, 5, -1, "deploy")):
        calib_loop, conf_loop, conf, selected = bad
        try:
            _mirror_gate_act(calib_loop, conf_loop, conf, selected)
            raise AssertionError(f"ill-formed conf must raise ValueError: {bad}")
        except ValueError:
            pass
    # ILL-FORMED: NEGATIVE loop indices — mirror of Nat semantics, never
    # silently accepted
    for bad in ((-1, 2, 84, "deploy"), (2, -1, 84, "deploy")):
        calib_loop, conf_loop, conf, selected = bad
        try:
            _mirror_gate_act(calib_loop, conf_loop, conf, selected)
            raise AssertionError(f"negative loop index must raise ValueError: {bad}")
        except ValueError:
            pass
    # non-string action (mirror of the vocabulary type)
    try:
        _mirror_gate_act(5, 5, 85, 99)
        raise AssertionError("non-string action must raise TypeError")
    except TypeError:
        pass


def _mirror_gate_tool(calib_loop, conf_loop, conf, selected):
    """Python mirror of gateTool: the payload is the SELECTED TOOL
    (never the confidence); below the threshold or at a wrong loop the
    gate abstains. Confidence validated on the [0,100] scale
    (mirror of `conf_le_100`), and strict-integer fields (mirror of
    Nat — negative loop indices are NOT silently accepted)."""
    if not (isinstance(selected, str) and type(conf) is int
            and type(calib_loop) is int and type(conf_loop) is int):
        raise TypeError("tool fields must be (str, int, int, int)")
    if not 0 <= conf <= 100:
        raise ValueError("ill-formed tool response: confidence off the [0,100] scale")
    if calib_loop < 0 or conf_loop < 0:
        raise ValueError("ill-formed tool response: negative loop index (mirror of Nat)")
    if calib_loop != conf_loop:
        return None
    return selected if tau_le(conf, calib_tau) else None


def test_tool_golden() -> None:
    """The Lean-exported tool collection: next-step selection from a
    declared duplicate-free vocabulary (membership and distinctness
    derived independently from the exported lists), the gate in ALL
    branches, and the payload being the TOOL identifier."""
    tools = V["tool_tools"]
    assert len(tools) == len(set(tools)) >= 1, (
        "the tool vocabulary must be non-empty and duplicate-free"
    )
    assert V["tool_selected"] in tools, (
        "the selected tool must be a member of the declared vocabulary"
    )
    assert V["tool_selected"] == "read" == tools[1], (
        "the demo selection is `read` (non-trivial index 1)"
    )
    # positive path: calib bound to loop 2, confidence from loop 2 (84 >= 75)
    assert V["tool_gate_positive"] == "decided", "positive path must decide"
    assert V["tool_gate_payload_positive"] == "read", (
        "the payload must be the TOOL identifier, not the confidence"
    )
    assert _mirror_gate_tool(2, 2, 84, "read") == V["tool_gate_payload_positive"]
    # the SCALE BOUNDARY case: τ = 100 with the constructed conf AT 100
    assert V["tool_gate_boundary"] == "decided", "boundary τ=100 must decide"
    assert V["tool_gate_payload_boundary"] == "read"
    assert _mirror_gate_tool(2, 2, 100, "read") == "read"
    # abstention: calib at loop 5, conf 20 < 75
    assert V["tool_gate"] == "none", "tool gate must defer below the threshold"
    assert _mirror_gate_tool(5, 5, 20, "read") is None
    # wrong loop: calib at 5, conf from loop 2 — abstains despite 84 >= 75
    # (the frozen field exercises the same case through the bridge)
    assert V["tool_gate_wrong_loop"] == "none", "wrong loop must abstain (frozen)"
    assert _mirror_gate_tool(5, 2, 84, "read") is None


def test_tool_rejects() -> None:
    """Negative and boundary cases (Python mirrors of the tool contract's
    theorems): below threshold the gate abstains (gateTool_defers_below);
    the deciding payload is the TOOL (gateTool_payload_is_tool); wrong
    loop abstains (gateTool_wrong_loop_never_decides); ill-formed
    responses — non-integer fields, confidence off the scale, negative
    loop indices, non-string tool — are REJECTED by validation."""
    tau = CALIBRATION_THRESHOLD
    # deferral below threshold — even for an attractive next step
    assert _mirror_gate_tool(5, 5, tau - 1, "read") is None
    # deciding payload is the tool, NOT the confidence
    assert _mirror_gate_tool(2, 2, tau, "read") == "read"
    assert _mirror_gate_tool(2, 2, 100, "write") == "write"
    # wrong loop abstains regardless of the confidence
    assert _mirror_gate_tool(5, 2, tau, "read") is None
    assert _mirror_gate_tool(5, 2, 100, "write") is None
    # TYPE rejections: non-integer confidence, non-integer loop indices
    for bad in ((5, 5, 85.0, "read"), (5, True, 85, "read")):
        calib_loop, conf_loop, conf, selected = bad
        try:
            _mirror_gate_tool(calib_loop, conf_loop, conf, selected)
            raise AssertionError(f"non-integer field must raise TypeError: {bad}")
        except TypeError:
            pass
    # ILL-FORMED: confidence off the scale
    for bad in ((5, 5, 101, "read"), (5, 5, -1, "read")):
        calib_loop, conf_loop, conf, selected = bad
        try:
            _mirror_gate_tool(calib_loop, conf_loop, conf, selected)
            raise AssertionError(f"ill-formed conf must raise ValueError: {bad}")
        except ValueError:
            pass
    # ILL-FORMED: NEGATIVE loop indices — mirror of Nat semantics
    for bad in ((-1, 2, 84, "read"), (2, -1, 84, "read")):
        calib_loop, conf_loop, conf, selected = bad
        try:
            _mirror_gate_tool(calib_loop, conf_loop, conf, selected)
            raise AssertionError(f"negative loop index must raise ValueError: {bad}")
        except ValueError:
            pass
    # non-string tool (mirror of the vocabulary type)
    try:
        _mirror_gate_tool(5, 5, 85, 99)
        raise AssertionError("non-string tool must raise TypeError")
    except TypeError:
        pass


# ---- Phase B/B2: reference adapter skeleton (issue #19) ----

def test_adapter_build_choice_noul() -> None:
    """Positive cases: both producing branches construct responses from
    REAL engine output (the reference engine's per-loop readout), the
    gate-visible fields are computed (conf = max(probs), first-max
    argmax), the noul branch yields exactly the YES/NO pair, objects
    carry no qtype field, and decide() at the honest call site mirrors
    gate_loop (conformance.py's own mirror) — same q, same response
    object, loop index read from the object."""
    ref = ReferenceEngine(V["state"])
    tau = CALIBRATION_THRESHOLD
    calib_choice = {"qtype": "choice", "loopIdx": 2, "tau": tau}
    calib_noul = {"qtype": "noul", "loopIdx": 3, "tau": tau}
    for t in (1, 2, SPEC_T):
        out = {
            "loopIdx": t,
            "declared": ["a", "b"],
            "probs": ref.probs_at(t),
        }
        # -- choice: the shared Response core, computed conf/argmax --
        r = adapter.build("choice", out)
        assert isinstance(r, adapter.ChoiceResponse)
        assert r.declared == ("a", "b") and r.probs == tuple(ref.probs_at(t))
        assert r.conf == max(r.probs) == ref.conf_at(t), (
            "conf must be computed as max(probs) — the mirror of binConf_is_top"
        )
        first_max = r.probs.index(r.conf)
        assert r.argmax == first_max == (0 if r.probs[0] >= 50 else 1), (
            "argmax must be the first index attaining the confidence"
        )
        assert not hasattr(r, "qtype"), (
            "no qtype field: the dispatch key selected the constructor "
            "(pairing by construction, not by a validator)"
        )
        # -- noul: same engine output relabeled to the declared pair --
        out_noul = {"loopIdx": t, "declared": ["YES", "NO"], "probs": ref.probs_at(t)}
        n = adapter.build("noul", out_noul)
        assert isinstance(n, adapter.NoulResponse)
        assert n.declared == ("YES", "NO"), "noul must carry the declared_pair"
        assert n.conf == max(n.probs) and n.conf == r.conf, (
            "same readout: noul conf = max(p, 100-p), identical to choice"
        )
        assert not hasattr(n, "qtype")
        # -- honest gate call site: decide() mirrors gate_loop --
        # (gate_loop mirrors Decision as "none"; decide mirrors the Option
        # as None — normalize before comparing)
        expected = gate_loop(calib_choice, {"qtype": "choice", "loopIdx": t,
                                            "conf": r.conf})
        expected = None if expected == "none" else expected
        assert adapter.decide(calib_choice, "choice", r) == expected, (
            "adapter decide() must agree with the gateLoop mirror at the "
            "honest call site"
        )
        n_gate = gate_loop(calib_noul, {"qtype": "noul", "loopIdx": t, "conf": n.conf})
        assert adapter.decide(calib_noul, "noul", n) == (
            None if n_gate == "none" else n_gate
        )
    # no calibration record: no decision (gateOptCalib none)
    r2 = adapter.build("choice", {"loopIdx": 2, "declared": ["a", "b"],
                                  "probs": ref.probs_at(2)})
    assert adapter.decide(None, "choice", r2) is None
    # wrong qtype / wrong loop at the call site: abstains (the conjunctive
    # guard has TWO conditions — the twin of wrong_type_structural and
    # wrong_loop_structural)
    tau_high = r2.conf  # WOULD decide absent the guards — setup assertion
    assert _gate_p(tau_high, r2.conf) == "argmax"
    assert adapter.decide({"qtype": "noul", "loopIdx": 2, "tau": tau_high},
                          "choice", r2) is None
    assert adapter.decide({"qtype": "choice", "loopIdx": 2 + 1, "tau": tau_high},
                          "choice", r2) is None
    # at its own type and loop: decides with the argmax payload semantics
    assert adapter.decide({"qtype": "choice", "loopIdx": 2, "tau": tau_high},
                          "choice", r2) == "argmax"
    # below the threshold: defers (gateCalib_defers_below)
    assert adapter.decide({"qtype": "choice", "loopIdx": 2, "tau": r2.conf + 1},
                          "choice", r2) is None
    # slice boundary: the later branches are EXPLICIT (NotImplementedError),
    # an unknown qtype is a ValueError — never a silent fallback
    for later in adapter.LATER_SLICES:
        try:
            adapter.build(later, {"loopIdx": 1, "declared": ["a", "b"],
                                  "probs": [50, 50]})
            raise AssertionError(f"{later!r} must raise NotImplementedError")
        except NotImplementedError:
            pass
    try:
        adapter.build("binary", {"loopIdx": 1, "declared": ["a", "b"],
                                 "probs": [50, 50]})
        raise AssertionError("unknown qtype must raise ValueError")
    except ValueError:
        pass


def test_adapter_rejects() -> None:
    """Rejection cases (issue #19 acceptance criteria): bool in int fields
    (strict `type(x) is int`, not isinstance), float/str values, out-of-
    bounds in BOTH directions, non-normalized weights, K < 2, duplicate
    declared options, wrong-vocabulary noul payload, negative loop index,
    and missing/ill-typed engine_output — every one a REJECTION
    (exception), never a silent coercion."""
    good = {"loopIdx": 3, "declared": ["a", "b"], "probs": [70, 30]}
    # baseline sanity: the good output builds on both branches
    assert adapter.build("choice", dict(good)).conf == 70
    assert adapter.build("noul", {**good, "declared": ["YES", "NO"]}).conf == 70

    def rejects(q, out, exc):
        try:
            adapter.build(q, out)
            raise AssertionError(f"{q}: ill-formed output must raise {exc.__name__}: {out}")
        except exc:
            pass

    # bool in int fields (bool is an int subclass — isinstance would pass)
    for out in (
        {**good, "probs": [True, 30]}, {**good, "probs": [70, False]},
        {**good, "loopIdx": True}, {**good, "declared": [True, "b"]},
    ):
        rejects("choice", out, TypeError)
    # float and str values in the distribution and the loop index
    for out in (
        {**good, "probs": [70.0, 30]}, {**good, "probs": ["70", 30]},
        {**good, "loopIdx": 3.0}, {**good, "loopIdx": "3"},
        {**good, "declared": ["a", 2]},
    ):
        rejects("choice", out, TypeError)
    # out-of-scale in BOTH directions (mirror of the [0,100] bounds)
    for bad_probs in ([101, -1], [-5, 105], [70, 31], [70, 29]):
        # [70,31]/[70,29]: sums 101/99 — non-normalized weights
        rejects("choice", {**good, "probs": bad_probs}, ValueError)
    # K < 2: one option is not a question (k_ge_2)
    rejects("choice", {"loopIdx": 3, "declared": ["a"], "probs": [100]}, ValueError)
    # duplicate declared options (declared_nodup)
    rejects("choice", {"loopIdx": 3, "declared": ["a", "a"], "probs": [50, 50]},
            ValueError)
    # declared/probs length mismatch
    rejects("choice", {"loopIdx": 3, "declared": ["a", "b", "c"], "probs": [50, 50]},
            ValueError)
    # negative loop index: mirror of Nat — never silently accepted
    rejects("choice", {**good, "loopIdx": -1}, ValueError)
    rejects("noul", {**good, "declared": ["YES", "NO"], "loopIdx": -2}, ValueError)
    # wrong-vocabulary noul payload: well-formed but NOT the declared pair
    for wrong in (["yes", "no"], ["YES"], ["A", "B"], ["YES", "NO", "MAYBE"]):
        if len(wrong) < 2 or len(set(wrong)) < 2:
            rejects("noul", {"loopIdx": 3, "declared": wrong,
                             "probs": [70, 30]}, ValueError)
        elif len(wrong) != 2:
            rejects("noul", {"loopIdx": 3, "declared": wrong,
                             "probs": [40, 30, 30]}, ValueError)
        else:
            rejects("noul", {"loopIdx": 3, "declared": wrong,
                             "probs": [70, 30]}, ValueError)
    # missing key / ill-typed engine_output
    rejects("choice", {"loopIdx": 3, "declared": ["a", "b"]}, KeyError)
    rejects("choice", [("loopIdx", 3)], TypeError)
    # decide(): bool tau / bool loopIdx in the calibration are rejected too
    r = adapter.build("choice", dict(good))
    for calib in ({"qtype": "choice", "loopIdx": 3, "tau": True},
                  {"qtype": "choice", "loopIdx": True, "tau": 75},
                  {"qtype": "choice", "loopIdx": 3, "tau": 101},
                  {"qtype": "choice", "loopIdx": 3, "tau": -1}):
        try:
            adapter.decide(calib, "choice", r)
            raise AssertionError(f"ill-formed calib must be rejected: {calib}")
        except (TypeError, ValueError) as e:
            assert type(e) in (TypeError, ValueError)
    # calib tau > 100 / < 0 raise ValueError specifically (scale bound)
    for calib in ({"qtype": "choice", "loopIdx": 3, "tau": 101},
                  {"qtype": "choice", "loopIdx": 3, "tau": -1}):
        try:
            adapter.decide(calib, "choice", r)
            raise AssertionError(f"tau off scale must raise ValueError: {calib}")
        except ValueError:
            pass


def test_adapter_bridge_report() -> None:
    """B3 bridge integration (issue #20): adapter output feeding the
    conformance report, differential against the frozen vectors (design
    §4 of docs/phase-b-adapter-design.md). For every pinned loop
    t = 1..T the reference engine's OWN per-loop readout goes through
    `adapter.build` (both binary branches) and `adapter.decide` at the
    honest call site; the computed conf/argmax and the gate outcome are
    asserted against the frozen vectors — computed from the constructed
    responses, never transcribed. Per request the report emits a record
    {qtype, loopIdx, gate, provenance}: provenance class `frozen` for
    every case a pinned vector validates, `unpinned` for report-only
    cases (none in this slice). The six frozen `gate_calib_cases` are
    re-derived THROUGH the adapter path (same calibrations as
    _gate_calib_cases: wrong-loop, wrong-type, no-record, below-τ,
    deciding τ₀−1, wrong-loop-with-deciding-τ)."""
    ref = ReferenceEngine(V["state"])
    tau0 = CALIBRATION_THRESHOLD
    report = []
    for t in range(1, SPEC_T + 1):
        for q in ("choice", "noul"):
            declared = ["YES", "NO"] if q == "noul" else ["opt0", "opt1"]
            out = {"loopIdx": t, "declared": declared,
                   "probs": ref.probs_at(t)}
            # the adapter's INPUT is the engine's own readout: differential
            # against the frozen distribution before anything is built
            assert ref.probs_at(t) == V["probs_trace"][t - 1], (
                f"engine readout != frozen probs at loop {t}"
            )
            r = adapter.build(q, out)
            assert r.probs == tuple(V["probs_trace"][t - 1])
            assert r.conf == V["conf_trace"][t - 1], (
                f"{q}: computed conf != frozen conf_trace at loop {t}"
            )
            assert r.argmax == r.probs.index(r.conf), (
                f"{q}: argmax must be the first index attaining the confidence"
            )
            calib = {"qtype": q, "loopIdx": t, "tau": tau0}
            got = adapter.decide(calib, q, r)
            # two independent expectations for the gate: the gateLoop
            # mirror of THIS suite on the constructed conf, and the
            # frozen gate_tau75 vector — adapter == mirror == frozen
            mirror = _gate_p(tau0, r.conf)
            assert got == (None if mirror == "none" else mirror), (
                f"{q}: adapter decide() != gateLoop mirror at loop {t}"
            )
            assert mirror == V["gate_tau75"][t - 1], (
                f"{q}: τ₀ gate of the constructed conf != frozen gate_tau75 at loop {t}"
            )
            report.append({"qtype": q, "loopIdx": t,
                           "gate": "none" if got is None else got,
                           "provenance": "frozen"})
    # report shape per design §4: exactly the four fields, every pinned
    # case validated three-way (provenance `frozen`), no unpinned record
    # in this slice, decision counts consistent with the frozen gate
    assert len(report) == 2 * SPEC_T
    for rec in report:
        assert set(rec) == {"qtype", "loopIdx", "gate", "provenance"}
        assert rec["provenance"] == "frozen"
        assert rec["gate"] in ("none", "argmax")
        assert rec["loopIdx"] == (report.index(rec) // 2) + 1
    decided = [rec for rec in report if rec["gate"] != "none"]
    # both branches share the readout, so both decide at exactly the
    # frozen τ₀ argmax loops (2 records per deciding loop)
    assert len(decided) == 2 * sum(1 for g in V["gate_tau75"] if g != "none")
    print(f"ADAPTER REPORT: {len(report)} records "
          f"(choice={sum(1 for x in report if x['qtype'] == 'choice')}, "
          f"noul={sum(1 for x in report if x['qtype'] == 'noul')}), "
          f"frozen-pinned={sum(1 for x in report if x['provenance'] == 'frozen')}, "
          f"unpinned=0, decided={len(decided)}, "
          f"abstained={len(report) - len(decided)}")

    # the six frozen gate_calib_cases, re-derived THROUGH the adapter
    # path — cases 2/3/6 exercise the conjunctive guard (wrong loop /
    # wrong type), case 4 is gateOptCalib none, case 5 DECIDES on τ₀−1
    def resp(t):
        return adapter.build(
            "choice", {"loopIdx": t, "declared": ["opt0", "opt1"],
                       "probs": ref.probs_at(t)})

    def gate_of(calib, q, r):
        got = adapter.decide(calib, q, r)
        return "none" if got is None else got

    conf3 = V["conf_trace"][2]
    conf5 = V["conf_trace"][4]
    conf8 = V["conf_trace"][SPEC_T - 1]
    calib3 = {"qtype": "choice", "loopIdx": 3, "tau": tau0}
    calib5 = {"qtype": "choice", "loopIdx": 5, "tau": tau0 - 1}
    calibD = {"qtype": "choice", "loopIdx": 3, "tau": conf8 - 1}
    cases = [
        gate_of(calib3, "choice", resp(3)),   # own loop, below τ₀
        gate_of(calib3, "choice", resp(8)),   # wrong loop
        gate_of(calib3, "act", resp(3)),      # wrong question type
        gate_of(None, "choice", resp(3)),     # no calibration record
        gate_of(calib5, "choice", resp(5)),   # own loop, DECIDING
        gate_of(calibD, "choice", resp(8)),   # wrong loop, τ would decide
    ]
    # setup assertions: the discriminating cases really discriminate —
    # their τ WOULD decide absent the binding the case is guarding
    assert _gate_p(tau0 - 1, conf5) == "argmax", (
        "case 5 must decide on its own τ"
    )
    assert _gate_p(conf8 - 1, conf8) == "argmax", (
        "case 6's τ would decide absent the loop guard"
    )
    assert cases == V["gate_calib_cases"], (
        f"adapter-path gate_calib_cases {cases} != frozen {V['gate_calib_cases']}"
    )
    assert _gate_p(tau0, conf3) == "none", (
        "case 1 must be a below-τ case, not a binding case"
    )

    # noul with its own calibration: decided iff conf >= τ at the own
    # loop — same conf as choice (shared readout), declared YES/NO pair
    n = adapter.build("noul", {"loopIdx": 5, "declared": ["YES", "NO"],
                               "probs": ref.probs_at(5)})
    assert n.declared == ("YES", "NO")
    assert adapter.decide({"qtype": "noul", "loopIdx": 5, "tau": tau0},
                          "noul", n) == "argmax"
    assert adapter.decide({"qtype": "noul", "loopIdx": 5,
                           "tau": V["conf_trace"][4] + 1}, "noul", n) is None


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
        test_act_golden,
        test_act_rejects,
        test_tool_golden,
        test_tool_rejects,
        test_adapter_build_choice_noul,
        test_adapter_rejects,
        test_adapter_bridge_report,
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
