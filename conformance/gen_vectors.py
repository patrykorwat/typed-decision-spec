#!/usr/bin/env python3
"""Derive and freeze the Tier-1 vectors (run once; output is sha256-pinned).

Spec math — mirrors TypedDecision/{Loop,Defer}.lean (v1.2):
  encode(text) = int(sha256(text)[:8], 16) % 2**31        # tokens encoded ONCE
  step(h)      = (A*h + B) % M                            # one stack pass
  read(t, h)   = (W*h + R*t) % 100                         # PER-LOOP readout
  resp(t)      = probs [p, 100-p], conf = max(p, 100-p)    # constructed Response
  confAt(t)    = conf(resp(t))                             # budgets 1..T
  isHard(K=2)  : 2*K*conf >= 100*(K+1)                     # eval boundary
  gate(tau)    : decide iff tau <= conf (gateP)            # calibration gate
  reinjected   : h_{t+1} = step(h_t) + h0                  # the WRONG engine

Every conf_trace entry is the confidence of a CONSTRUCTED normalized
binary response (>= 50 for K=2), so the trace and the Response contract
are connected by construction (P1-1). The same math is ALSO computed by
conformance/ExportVectors.lean straight from the Lean definitions
(`runBin`, `isHard`, `gateP`, `spec_T`); conformance.py asserts
frozen == Lean == Python.
"""
import hashlib
import json
from pathlib import Path

A, B, M, W, R, T = 1103515245, 12345, 2**31, 5, 7, 8
STATE = "Zgloszenie naprawy windy, wejscie serwerownia 3p."


def encode(text: str) -> int:
    return int(hashlib.sha256(text.encode()).hexdigest()[:8], 16) % M


def step(h: int) -> int:
    return (A * h + B) % M


def read(t: int, h: int) -> int:
    return (W * h + R * t) % 100


def bin_probs(h0: int, t: int) -> list:
    """The constructed binary response's probs at loop t: [p, 100-p]."""
    h = h0
    for _ in range(t):
        h = step(h)
    p = read(t, h)
    return [p, 100 - p]


def bin_conf(h0: int, t: int) -> int:
    """Confidence of the constructed binary response at loop t."""
    p, q = bin_probs(h0, t)
    return max(p, q)


def reinjected_bin_conf(h0: int, t: int) -> int:
    """The wrong engine's scalar trace (mirror of Lean's reinjectedRun:
    raw per-loop readout, not the response-derived confidence)."""
    h = h0
    for _ in range(t):
        h = step(h) + h0
    return read(t, h)


def is_hard(k: int, conf: int) -> bool:
    """The spec's isHard predicate, as implemented (mirror of Defer.lean)."""
    return 2 * k * conf >= 100 * (k + 1)


def gate_p(tau: int, conf: int) -> str:
    """The spec's shared gate predicate gateP (mirror of Defer.lean)."""
    return "argmax" if tau <= conf else "none"


def main() -> None:
    h0 = encode(STATE)
    # budgets 1..T (SanSi §3) — h_0 is the token encoding, not a readout
    conf = [bin_conf(h0, t) for t in range(1, T + 1)]
    probs = [bin_probs(h0, t) for t in range(1, T + 1)]
    reinj = [reinjected_bin_conf(h0, t) for t in range(1, T + 1)]
    vectors = {
        "spec": "typed-decision-spec v1.2",
        "note": "derived from the spec definitions, frozen; never from an engine",
        "pin": {"A": A, "B": B, "M": M, "W": W, "R": R, "T": T,
                "calibration_threshold": 75},
        "state": STATE,
        "h0": h0,
        "conf_trace": conf,
        "probs_trace": probs,
        "is_hard_K2": [is_hard(2, c) for c in conf],
        "gate_tau75": [gate_p(75, c) for c in conf],
        "reinjected_conf_trace": reinj,
    }
    out = Path(__file__).resolve().parent.parent / "test-vectors" / "tier1.json"
    out.parent.mkdir(parents=True, exist_ok=True)
    canon = json.dumps(
        vectors, sort_keys=True, ensure_ascii=False, separators=(",", ":")
    ).encode()
    vectors["vectors_sha256"] = hashlib.sha256(canon).hexdigest()
    out.write_text(json.dumps(vectors, indent=1, ensure_ascii=False) + "\n", encoding="utf-8")
    print(f"frozen {out} sha256={vectors['vectors_sha256']}")


if __name__ == "__main__":
    main()
