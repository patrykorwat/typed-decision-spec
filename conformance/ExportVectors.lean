import TypedDecision.Loop

/-!
# Executable conformance export (the formal half of the bridge)

Computes the Tier-1 expected values FROM the spec's definitions
(`iter`, `confAt`, `run`, `isHard`, gate semantics) — so the frozen
vectors are checked against the same functions that are proved about,
closing the "Python implements its own math" gap.

Usage (from the repo root):
  lake env lean --run conformance/ExportVectors.lean A B M W T H0 TAU

Prints one JSON object on stdout.
-/

open TypedDecision

def parseNat (s : String) : Nat := s.toNat!

def main (args : List String) : IO UInt32 := do
  match args with
  | [a, b, m, w, t, h0, tau] =>
    let A := parseNat a
    let B := parseNat b
    let M := parseNat m
    let W := parseNat w
    let T := parseNat t
    let H0 := parseNat h0
    let TAU := parseNat tau
    -- the spec's definitions, instantiated with the pin
    let F : Nat → Nat := fun h => (A * h + B) % M
    let read : Nat → Nat → Pct := fun _ h => (W * h) % 100
    -- budgets 1..T, straight from `run`
    let trace := (List.range T).map (fun i => confAt read F H0 (i + 1))
    -- the reinjected counterengine, same tokens = h0
    let reinj := (List.range T).map
      (fun i => read (i + 1) (iter (fun h => F h + H0) (i + 1) H0))
    -- eval boundary (isHard, K = 2) and the calibration gate at TAU
    let hard := trace.map (fun c => decide (2 * 2 * c ≥ 100 * (2 + 1)))
    let gates := trace.map (fun c => if TAU ≤ c then "argmax" else "none")
    -- List String toString drops the quotes; re-add them for valid JSON
    let gatesQ := toString (gates.map (fun s => "\"" ++ s ++ "\""))
    let j := "{\"conf_trace\": " ++ toString trace
      ++ ", \"reinjected_conf_trace\": " ++ toString reinj
      ++ ", \"is_hard_K2\": " ++ toString hard
      ++ ", \"gate_tau\": " ++ gatesQ ++ "}"
    IO.println j
    return 0
  | _ => do
    IO.eprintln "usage: ExportVectors A B M W T H0 TAU"
    return 1
