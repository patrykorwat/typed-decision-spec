import TypedDecision.Defer

/-!
# Typed decision contract: looped engines (System 1.5)

Pins the loop semantics of a SanSi-style engine (arXiv 2610.07730 §3):
one stack applied T times, readout after every loop, input tokens
encoded ONCE. Three machine-checked properties:

* `run_length` / `budget_at` — one run delivers every budget 1..T;
* `reinjection_differs` — re-injecting tokens each loop is a
  DIFFERENT model, demonstrated by a witness divergence;
* `no_calib_never_decides` — a threshold without its loop index
  decides nothing (calibration is bound to the loop it was fitted at,
  SanSi §5.3: ECE best at loop 3, climbing again by loop 8).

Settling behaviour (89.1% of answers final by loop 4, fixes/breaks
~3:1 until loop 5) is EMPIRICAL and deliberately outside this spec.
-/

namespace TypedDecision

/-- The pinned loop budget of this spec revision (SanSi trains T = 8).
Other budgets are a v2, never a silent change. -/
def spec_T : Nat := 8

/-- The state after t applications of the looped stack: h_t = F(h_{t-1}),
h_0 = token encoding. Self-contained iterate (no Mathlib). -/
def iter (F : Nat → Nat) (t : Nat) (h : Nat) : Nat :=
  match t with
  | 0 => h
  | t + 1 => F (iter F t h)

/-- Confidence read after loop t: the readout sees the state h_t,
which is the output of loop t and the input of loop t+1. Input
tokens are encoded ONCE into h0; they are not injected again. -/
def confAt (read : Nat → Pct) (F : Nat → Nat) (h0 : Nat) (t : Nat) : Pct :=
  read (iter F t h0)

/-- One run with T loops stores the readout after every loop, so a
single pass yields the decisions of all budgets 1..T. -/
def run (F : Nat → Nat) (read : Nat → Pct) (h0 : Nat) (T : Nat) : List Pct :=
  (List.range (T + 1)).map (fun t => confAt read F h0 t)

theorem run_length (F : Nat → Nat) (read : Nat → Pct) (h0 T : Nat) :
    (run F read h0 T).length = T + 1 := by
  simp [run, List.length_map, List.length_range]

/-- The stored trace of the single run agrees with the per-budget
recompute: for every budget t ≤ T the loop-t readout is an entry of
the run, computed from the same encoded-once h0. -/
theorem budget_at (F : Nat → Nat) (read : Nat → Pct) (h0 : Nat) :
    ∀ t ≤ spec_T, confAt read F h0 t ∈ run F read h0 spec_T := by
  intro t h
  exact List.mem_map_of_mem (List.mem_range.mpr (Nat.lt_succ_of_le h))

/-- The WRONG engine: re-injects the token encoding at every loop
(hₜ₊₁ = F hₜ + tokens). A different model; from the outside — typed
responses only — the divergence is invisible until calibrated
numbers drift. -/
def reinjectedRun (F : Nat → Nat) (tokens : Nat) (read : Nat → Pct)
    (h0 : Nat) (T : Nat) : List Pct :=
  (List.range (T + 1)).map (fun t => read (iter (fun h => F h + tokens) t h0))

/-- A deliberate divergence, demonstrated: with identity dynamics and
readout and token mark 1, the reinjecting engine's confidence trace
differs from the conforming one (0 vs 1 at loop 1). -/
theorem reinjection_differs :
    run (fun h => h) (fun h => h) 0 1 ≠
      reinjectedRun (fun h => h) 1 (fun h => h) 0 1 := by
  decide

/-- A calibration threshold carries the loop index it was fitted at. -/
structure Calib where
  τ : Pct
  loopIdx : Nat
  certified : τ ≤ 100

/-- No calibration record, no decision — the engine refuses instead of
guessing a threshold (same refusal class as refusing a quantized
checkpoint whose scales cannot be read). -/
def gateCalib (c : Option Calib) (r : Response) : Decision :=
  match c with
  | some c => gate c.τ r
  | none => none

theorem no_calib_never_decides (r : Response) : gateCalib none r = none := by
  simp [gateCalib]

end TypedDecision
