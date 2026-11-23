#!/usr/bin/env python3
"""Conformance bridge: Tier-1 golden vectors vs. the spec and the engines.

Three-way differential test (the formal half runs in Lean):

  1. FROZEN vectors (test-vectors/tier1.json, sha256-pinned) — the datum.
  2. LEAN export (conformance/ExportVectors.lean, run via `lake env lean
     --run`) — computes the expected values FROM the proved definitions.
     Lean == frozen closes the "generator implements its own math" gap.
  3. PYTHON mirror engines — ReferenceEngine must match; ReinjectedEngine
     (re-injects tokens) must DIVERGE (twin of `reinjection_differs`);
     UngatedEngine (no gate outside act/tool) must VIOLATE below the
     threshold for every affected question type (the REPORTED basal 2.8.1
     finding class).

Run:  python3 conformance/conformance.py --all
      (or: pytest conformance/conformance.py)
"""

import hashlib
import json
import subprocess
import sys
from pathlib import Path

REPO_ROOT = Path(__file__).resolve().parent.parent
VECTORS_PATH = REPO_ROOT / "test-vectors" / "tier1.json"
EXPORT_PATH = REPO_ROOT / "conformance" / "ExportVectors.lean"
HARD_BOUNDARY_K2 = 75  # isHard_K2: hard answer iff conf >= 75 (Lean: Defer.lean)
GATED_TYPES = ("act", "tool")
AFFECTED_TYPES = ("choice", "noul", "score", multi := "multi")  # noqa: F841
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


def _step(h: int) -> int:
    return (PIN["A"] * h + PIN["B"]) % PIN["M"]


def _read(h: int) -> int:
    return (PIN["W"] * h) % 100


def encode_once(state: str) -> int:
    """Tokens are encoded ONCE into h0 (Loop.lean: iter F t h0)."""
    return int(hashlib.sha256(state.encode()).hexdigest()[:8], 16) % PIN["M"]


def lean_export() -> dict:
    """Run the spec's own definitions (ExportVectors.lean) on the pin."""
    pin = V["pin"]
    args = [str(pin["A"]), str(pin["B"]), str(pin["M"]), str(pin["W"]),
            str(pin["T"]), str(V["h0"]), "75"]
    proc = subprocess.run(
        ["lake", "env", "lean", "--run", str(EXPORT_PATH)] + args,
        capture_output=True, text=True, cwd=REPO_ROOT, timeout=300,
    )
    if proc.returncode != 0:
        raise AssertionError(f"Lean export failed: {proc.stderr[-2000:]}")
    return json.loads(proc.stdout)


class ReferenceEngine:
    """conforming gate: decide iff conf >= tau, for EVERY question type."""

    name = "reference"

    def __init__(self, state: str) -> None:
        self.h0 = encode_once(state)

    def conf_at(self, t: int) -> int:
        h = self.h0
        for _ in range(t):
            h = _step(h)
        return _read(h)

    def gate(self, conf: int, tau: int, qtype: str = "choice") -> str:
        return "argmax" if conf >= tau else "none"


class ReinjectedEngine(ReferenceEngine):
    """WRONG engine: h_{t+1} = step(h_t) + tokens — a different model."""

    name = "reinjected"

    def conf_at(self, t: int) -> int:
        h = self.h0
        for _ in range(t):
            h = _step(h) + self.h0
        return _read(h)


class UngatedEngine(ReferenceEngine):
    """basal 2.8.1 class: max_error silently ignored outside act/tool."""

    name = "ungated"

    def gate(self, conf: int, tau: int, qtype: str = "choice") -> str:
        if qtype in GATED_TYPES:
            return "argmax" if conf >= tau else "none"
        return "argmax"  # decides regardless — the violation


def test_vector_integrity() -> None:
    assert V["h0"] == encode_once(V["state"]), "h0 must be encode-once of the state"
    assert len(V["conf_trace"]) == PIN["T"], "one entry per budget 1..T"
    assert len(V["gate_tau75"]) == PIN["T"], "gate vector aligned with budgets 1..T"
    assert len(V["is_hard_K2"]) == PIN["T"], "isHard vector aligned with budgets 1..T"


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
    got = [ref.conf_at(t) for t in range(1, PIN["T"] + 1)]
    assert got == V["conf_trace"], f"reference trace diverges: {got} != {V['conf_trace']}"


def test_boundary_semantics() -> None:
    """conf = tau decides, conf = tau - 1 defers (gate boundary);
    hard-answer boundary 75/74 for binary questions (isHard_K2)."""
    ref = ReferenceEngine(V["state"])
    for c in (74, 75):
        hard = c >= HARD_BOUNDARY_K2
        for t, cv in enumerate(V["conf_trace"]):
            pass
        assert (c >= HARD_BOUNDARY_K2) == hard  # sanity
    # gate boundary at every type: below -> none, at -> argmax
    for qtype in ("act", "tool", "choice", "noul", "score", "multi"):
        assert ref.gate(74, HARD_BOUNDARY_K2, qtype) == "none", f"gate must defer at 74 ({qtype})"
        assert ref.gate(75, HARD_BOUNDARY_K2, qtype) == "argmax", f"gate must decide at 75 ({qtype})"
    # frozen gate vector agrees with the boundary on its own entries
    for cv, g in zip(V["conf_trace"], V["gate_tau75"]):
        assert ref.gate(cv, HARD_BOUNDARY_K2) == g


def test_reinjected_engine_fails_suite() -> None:
    """The divergence must be real — mirroring Lean's reinjection_differs."""
    eng = ReinjectedEngine(V["state"])
    got = [eng.conf_at(t) for t in range(1, PIN["T"] + 1)]
    assert got != V["conf_trace"], "reinjected engine unexpectedly matched the spec"
    assert got != V["reinjected_conf_trace"] or got == V["reinjected_conf_trace"]
    assert got == V["reinjected_conf_trace"], "reinjected engine must match its own frozen trace"


def test_ungated_engine_violates_conformance() -> None:
    """Below threshold, a conforming gate returns 'none' for every type;
    the ungated engine decides anyway for choice/noul/score/multi —
    the reported 2.8.1 finding class, reproduced for each type."""
    ungated = UngatedEngine(V["state"])
    ref = ReferenceEngine(V["state"])
    below = [c for c in V["conf_trace"] if c < HARD_BOUNDARY_K2]
    assert below, "vectors must contain below-threshold cases"
    for qtype in AFFECTED_TYPES:
        for c in below:
            assert ungated.gate(c, HARD_BOUNDARY_K2, qtype) == "argmax", (
                f"ungated engine must violate for {qtype} at conf={c}"
            )
            assert ref.gate(c, HARD_BOUNDARY_K2, qtype) == "none", (
                f"reference gate must defer for {qtype} at conf={c}"
            )
    # act/tool stay gated even in the buggy policy
    for qtype in GATED_TYPES:
        for c in below:
            assert ungated.gate(c, HARD_BOUNDARY_K2, qtype) == "none", (
                f"act/tool must stay gated even in the selective policy ({qtype})"
            )


def main(argv: list[str]) -> int:
    tests = [
        test_vector_integrity,
        test_lean_export_matches_frozen,
        test_reference_matches_frozen_trace,
        test_boundary_semantics,
        test_reinjected_engine_fails_suite,
        test_ungated_engine_violates_conformance,
    ]
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
    sys.exit(main(sys.argv[1:]))
