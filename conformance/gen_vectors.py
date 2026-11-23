#!/usr/bin/env python3
"""Derive Tier-1 vectors from the spec's pinned integer math (run once;
output is frozen into test-vectors/tier1.json and sha256-pinned).

Spec math (mirrors TypedDecision/Loop.lean and TypedDecision/Defer.lean):
  encode(text) = int(sha256(text)[:8], 16) % 2**31        # tokens encoded ONCE
  step(h)      = (A*h + B) % M                            # one stack pass
  read(h)      = (W*h) % 100                              # confidence, percentage
  confAt(t)    = read(step^[t](h0))                       # loop-t readout
  isHard(K=2)  : conf >= 75
  gate(tau)    : decide iff conf >= tau
  reinjected   : h_{t+1} = step(h_t) + h0                 # the WRONG engine
"""
import hashlib
import json
from pathlib import Path

A, B, M, W, T = 1103515245, 12345, 2**31, 5, 8
STATE = "Zgloszenie naprawy windy, wejscie serwerownia 3p."


def encode(text: str) -> int:
    return int(hashlib.sha256(text.encode()).hexdigest()[:8], 16) % M


def step(h: int) -> int:
    return (A * h + B) % M


def read(h: int) -> int:
    return (W * h) % 100


def conf_at(h0: int, t: int) -> int:
    h = h0
    for _ in range(t):
        h = step(h)
    return read(h)


def reinjected_conf_at(h0: int, t: int) -> int:
    h = h0
    for _ in range(t):
        h = step(h) + h0
    return read(h)


def main() -> None:
    h0 = encode(STATE)
    conf = [conf_at(h0, t) for t in range(T + 1)]
    reinj = [reinjected_conf_at(h0, t) for t in range(T + 1)]
    vectors = {
        "spec": "typed-decision-spec v1",
        "note": "derived from the spec definitions, frozen; never from an engine",
        "pin": {"A": A, "B": B, "M": M, "W": W, "T": T},
        "state": STATE,
        "h0": h0,
        "conf_trace": conf,
        "is_hard_K2": [c >= 75 for c in conf],
        "gate_tau75": ["none" if c < 75 else "argmax" for c in conf],
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
