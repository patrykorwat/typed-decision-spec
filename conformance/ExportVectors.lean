import TypedDecision.Loop

/-!
# Executable conformance export (the formal half of the bridge)

Computes the Tier-1 expected values FROM the spec's definitions —
`runBin` (not a re-derived map), `isHard` via its Decidable instance
(not a duplicated formula), the shared `gateP` predicate, and the
pinned `spec_T` (a CLI T different from spec_T is REJECTED, so the
frozen budget cannot drift silently).

Usage (from the repo root):
  lake env lean --run conformance/ExportVectors.lean A B M W R H0 TAU

The readout is per-loop: read t h = (W*h + R*t) % 100 — the loop index
participates, so misassigned heads are detectable (P1-4).

Prints one JSON object on stdout.
-/

open TypedDecision

def parseNat (s : String) : Nat := s.toNat!

def main (args : List String) : IO UInt32 := do
  match args with
  | [a, b, m, w, r, h0, tau] =>
    let A := parseNat a
    let B := parseNat b
    let M := parseNat m
    let W := parseNat w
    let R := parseNat r
    let H0 := parseNat h0
    let TAU := parseNat tau
    -- the CLI carries no T: the spec's spec_T is the single source
    let F : Nat → Nat := fun h => (A * h + B) % M
    let rd : Nat → Nat → Pct := fun t h => (W * h + R * t) % 100
    -- bounded by construction: x % 100 ≤ 99 < 100
    have hmod : ∀ x : Nat, x % 100 ≤ 100 := fun x => Nat.le_of_lt (Nat.mod_lt x (by omega))
    let read : Readout := ⟨rd, fun t h => hmod (W * h + R * t)⟩
    -- budgets 1..T, straight from `runBin`
    let trace := runBin F read H0 spec_T
    -- the reinjected counterengine, same tokens = h0
    let reinj := reinjectedRun F H0 rd H0 spec_T
    -- eval boundary (isHard, K = 2) on the DEFINITION, and the shared
    -- gate predicate at TAU
    let hard := trace.map (fun c => decide (isHard 2 c))
    let gates := trace.map (fun c => if gateP TAU c then "argmax" else "none")
    -- List String toString drops the quotes; re-add them for valid JSON
    let gatesQ := toString (gates.map (fun s => "\"" ++ s ++ "\""))
    let j := "{\"conf_trace\": " ++ toString trace
      ++ ", \"reinjected_conf_trace\": " ++ toString reinj
      ++ ", \"is_hard_K2\": " ++ toString hard
      ++ ", \"gate_tau\": " ++ gatesQ ++ "}"
    IO.println j
    return 0
  | _ => do
    IO.eprintln "usage: ExportVectors A B M W R H0 TAU"
    return 1
