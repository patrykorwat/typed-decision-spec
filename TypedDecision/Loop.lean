import TypedDecision.Defer

/-!
# Typed decision contract: looped engines (System 1.5)

Pins the loop semantics of a SanSi-style engine (arXiv 2610.07730 §3):
one stack applied T times, readout after every loop (per-loop head:
W+U_tV_t, τ_t), input tokens encoded ONCE. Machine-checked properties:

* `run_length` / `budget_at` — one run delivers every budget 1..T,
  and budget t's readout sits at INDEX t-1 of the trace (exact
  position, not mere membership);
* `reinjection_differs` — re-injecting tokens each loop is a
  DIFFERENT model, demonstrated by a witness divergence;
* `wrong_loop_never_decides` / `no_calib_never_decides` — a calibration
  applies only at its own loop index; without a calibration record the
  engine refuses (SanSi §5.3: ECE best at loop 3, climbing again by
  loop 8 — calibration is bound to the loop it was fitted at).

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

/-- Confidence read after loop t. The readout is PER LOOP (SanSi §3:
p_t = softmax((W+U_tV_t)z_t/τ_t)), so the read is indexed by the loop
index as well as the state. Input tokens are encoded ONCE into h0; they
are not injected again. -/
def confAt (read : Nat → Nat → Pct) (F : Nat → Nat) (h0 : Nat) (t : Nat) : Pct :=
  read t (iter F t h0)

/-- One run with T loops yields the readouts for budgets 1..T
(SanSi §3: h_t = N(F(h_{t-1})), t = 1..T). The initial h_0 is the
token encoding, not a readout after a loop, so it is not an entry. -/
def run (F : Nat → Nat) (read : Nat → Nat → Pct) (h0 : Nat) (T : Nat) : List Pct :=
  (List.range T).map (fun i => confAt read F h0 (i + 1))

theorem run_length (F : Nat → Nat) (read : Nat → Nat → Pct) (h0 T : Nat) :
    (run F read h0 T).length = T := by
  simp [run, List.length_map, List.length_range]

/-- Budget t's readout sits at index t-1 of the trace — the exact
position a consumer must use, not mere membership. -/
theorem budget_at (F : Nat → Nat) (read : Nat → Nat → Pct) (h0 T : Nat) :
    ∀ i < T, (run F read h0 T)[i]? = some (confAt read F h0 (i + 1)) := by
  intro i hi
  have hr : run F read h0 T = (List.range T).map (fun t => confAt read F h0 (t + 1)) := rfl
  rw [hr, List.getElem?_map]
  have h1 : (List.range T)[i]? = some i := List.getElem?_range hi
  rw [h1]
  rfl

/-- The WRONG engine: re-injects the token encoding at every loop
(hₜ₊₁ = F hₜ + tokens). A different model; from the outside — typed
responses only — the divergence is invisible until calibrated
numbers drift. -/
def reinjectedRun (F : Nat → Nat) (tokens : Nat) (read : Nat → Nat → Pct)
    (h0 : Nat) (T : Nat) : List Pct :=
  (List.range T).map (fun i => read (i + 1) (iter (fun h => F h + tokens) (i + 1) h0))

/-- A deliberate divergence, demonstrated: with identity dynamics and
readout and token mark 1, the reinjecting engine's confidence trace
differs from the conforming one (0 vs 1 at loop 1). -/
theorem reinjection_differs :
    run (fun h => h) (fun _ h => h) 0 1 ≠
      reinjectedRun (fun h => h) 1 (fun _ h => h) 0 1 := by
  decide

/-- A calibration threshold: question-type-specific, carries the loop
index it was fitted at. `certified` is only the structural bound of the
stored number — whether τ is actually statistically certified is
empirical and outside this model. -/
structure Calib where
  qtype : QType
  τ : Pct
  loopIdx : Nat
  certified : τ ≤ 100

/-- The gate bound to its calibration: a calibration may only gate a
response of ITS OWN question type from ITS OWN loop index; anything
else defers (no valid calibration, no decision). -/
def gateCalib (c : Calib) (ty : QType) (t : Nat) (r : Response) : Decision :=
  if c.qtype = ty ∧ c.loopIdx = t then gate ty c.τ r else none

/-- Wrong loop: the calibration does not apply, the engine defers. -/
theorem wrong_loop_never_decides (c : Calib) (ty : QType) (t : Nat) (r : Response)
    (h : c.loopIdx ≠ t) : gateCalib c ty t r = none := by
  simp only [gateCalib]
  exact if_neg (fun hc => h hc.2)

/-- No calibration record, no decision — the engine refuses instead of
guessing a threshold (same refusal class as refusing a quantized
checkpoint whose scales cannot be read). -/
def gateOptCalib (c : Option Calib) (ty : QType) (t : Nat) (r : Response) : Decision :=
  match c with
  | some c => gateCalib c ty t r
  | none => none

theorem no_calib_never_decides (ty : QType) (t : Nat) (r : Response) :
    gateOptCalib none ty t r = none := by
  simp [gateOptCalib]

end TypedDecision
