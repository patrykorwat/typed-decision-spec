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

    def conf_at(self, t: int) -> int:
        h = self.h0
        for _ in range(t):
            h = _step(h)
        return max(_read(t, h), 100 - _read(t, h))

    def gate(self, conf: int, tau: int, qtype: str = "choice") -> str:
        return _gate_p(tau, conf)


class ReinjectedEngine(ReferenceEngine):
    """WRONG engine: h_{t+1} = step(h_t) + tokens — a different model.
    Its trace is the SCALAR per-loop readout (mirror of Lean's
    reinjectedRun), not the response-derived confidence."""

    name = "reinjected"

    def conf_at(self, t: int) -> int:
        h = self.h0
        for _ in range(t):
            h = _step(h) + self.h0
        return _read(t, h)


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


def gate_calib(calib: dict, qtype: str, t: int, conf: int) -> str:
    """Mirror of gateCalib (Loop.lean): a calibration applies only at its
    own question type and loop index; otherwise no decision."""
    if calib["qtype"] == qtype and calib["loopIdx"] == t:
        return _gate_p(calib["tau"], conf)
    return "none"


def test_vector_integrity() -> None:
    assert V["h0"] == encode_once(V["state"]), "h0 must be encode-once of the state"
    assert PIN["T"] == SPEC_T, "frozen budget must equal the pinned spec_T"
    for key in ("conf_trace", "probs_trace", "gate_tau75", "is_hard_K2",
                "reinjected_conf_trace"):
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


def test_lean_export_matches_frozen() -> None:
    """The proved definitions, executed, must reproduce the frozen vectors."""
    lean = lean_export()
    assert lean["conf_trace"] == V["conf_trace"], "Lean trace != frozen trace"
    assert lean["reinjected_conf_trace"] == V["reinjected_conf_trace"], (
        "Lean reinjected trace != frozen"
    )
    assert lean["is_hard_K2"] == V["is_hard_K2"], "Lean isHard != frozen"
    assert lean["gate_tau"] == V["gate_tau75"], "Lean gate != frozen gate"


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
    """The divergence must be real — mirroring Lean's reinjection_differs."""
    eng = ReinjectedEngine(V["state"])
    got = [eng.conf_at(t) for t in range(1, SPEC_T + 1)]
    assert got != V["conf_trace"], "reinjected engine unexpectedly matched the spec"
    assert got == V["reinjected_conf_trace"], "reinjected engine must match its own frozen trace"


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
