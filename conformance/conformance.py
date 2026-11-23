#!/usr/bin/env python3
"""Conformance bridge: Tier-1 golden vectors vs. engine implementations.

Structure mirrors sejmbench docs/lean: the vectors are derived from the
SPEC's definitions (never from an engine), frozen in test-vectors/tier1.json
and sha256-checked. Three engines are exercised:

  * ReferenceEngine  — implements the spec math; MUST match every vector.
  * ReinjectedEngine — re-injects tokens each loop; MUST diverge from the
    frozen trace (the machine-checked twin of `reinjection_differs`).
  * UngatedEngine    — skips the confidence gate for non-act types; MUST
    violate conformance below the threshold (the basal 2.8.1 bug class).

Run:  python3 conformance/conformance.py --all
      (or: pytest conformance/conformance.py)
"""

import hashlib
import json
import sys
from pathlib import Path

VECTORS_PATH = Path(__file__).resolve().parent.parent / "test-vectors" / "tier1.json"
HARD_BOUNDARY_K2 = 75  # isHard_K2: hard answer iff conf >= 75 (Lean: Defer.lean)


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
        if qtype in ("act", "tool"):
            return "argmax" if conf >= tau else "none"
        return "argmax"  # decides regardless — the violation


def test_vector_integrity() -> None:
    assert V["h0"] == encode_once(V["state"]), "h0 must be encode-once of the state"
    assert len(V["conf_trace"]) == PIN["T"] + 1, "one entry per budget 0..T"


def test_reference_matches_frozen_trace() -> None:
    ref = ReferenceEngine(V["state"])
    got = [ref.conf_at(t) for t in range(PIN["T"] + 1)]
    assert got == V["conf_trace"], f"reference trace diverges: {got} != {V['conf_trace']}"


def test_reference_hard_boundary_and_gate() -> None:
    ref = ReferenceEngine(V["state"])
    for t, c in enumerate(V["conf_trace"]):
        assert ref.conf_at(t) == c
        assert (c >= HARD_BOUNDARY_K2) == V["is_hard_K2"][t], f"isHard mismatch at t={t}"
        assert ref.gate(c, HARD_BOUNDARY_K2) == V["gate_tau75"][t], f"gate mismatch at t={t}"


def test_reinjected_engine_fails_suite() -> None:
    """The divergence must be real — mirroring Lean's reinjection_differs."""
    eng = ReinjectedEngine(V["state"])
    got = [eng.conf_at(t) for t in range(PIN["T"] + 1)]
    assert got != V["conf_trace"], "reinjected engine unexpectedly matched the spec"
    # and it must differ exactly where the spec says: from loop 1 on
    assert got[0] == V["conf_trace"][0], "loop 0 must agree (both start at h0)"
    assert got[1:] != V["conf_trace"][1:], "divergence must appear from loop 1"


def test_ungated_engine_violates_conformance() -> None:
    """Below threshold, a conforming gate returns 'none' for every type;
    the ungated engine decides anyway — the 2.8.1 finding, reproduced."""
    ungated = UngatedEngine(V["state"])
    below = [c for c in V["conf_trace"] if c < HARD_BOUNDARY_K2]
    assert below, "vectors must contain below-threshold cases"
    for c in below:
        assert ungated.gate(c, HARD_BOUNDARY_K2, "choice") == "argmax", (
            "ungated engine must violate (that is the demonstrated bug class)"
        )
        assert ReferenceEngine(V["state"]).gate(c, HARD_BOUNDARY_K2, "choice") == "none", (
            "reference gate must defer below threshold"
        )


def main(argv: list[str]) -> int:
    tests = [
        test_vector_integrity,
        test_reference_matches_frozen_trace,
        test_reference_hard_boundary_and_gate,
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
    if "--all" in argv or not argv:
        return 1 if failures else 0
    return 1 if failures else 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
