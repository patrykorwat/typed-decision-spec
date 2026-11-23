import TypedDecision.Basic

/-!
# Typed decision contract: confidence gating and deferral

Pins the escalation semantics. The normative content is `Conforming`:
BELOW the certified threshold, a gate returns NO decision (`none`) —
now typed by `QType`, so the claim covers every question type.

Three thresholds are deliberately kept apart:

* `HardAnswerThreshold` (`isHard`, evaluation — SanSi §4 metrics):
  an unanswerable item is right when the model gives no hard answer,
  i.e. its top probability is below (1 + 1/K)/2. Evaluation-only.
* `CalibrationThreshold` (`Calib.τ`, Loop.lean — operational): comes
  from `basal-calibrate`, is question-type-specific, and its
  statistical certification is empirical (outside this model).
* `DecisionGate` (`gate`): the policy consuming a calibration.

The `selectiveGate` witness encodes the REPORTED basal 2.8.1 finding
(observed on a live 2.8.1 server, 2026-11: `max_error` accepted in the
payload, zero deferrals below the certified threshold; note the
published v2.8.1 API docs describe `max_error` for choice/noul/score
with an `abstain` result field — that docs/behavior gap is itself part
of the finding). Independent HTTP reproduction: pending.
-/

namespace TypedDecision

/-- The engine's answer to one question: either the chosen option index,
or no decision. -/
@[reducible] def Decision := Option Nat

/-- Question types of the contract. -/
inductive QType
  | act | tool | choice | noul | score | multi
  deriving DecidableEq, Repr

/-- The conforming gate: decide only at or above the threshold —
for EVERY question type. -/
def gate (ty : QType) (τ : Pct) (r : Response) : Decision :=
  if τ ≤ r.conf then some r.argmax else none

/-- A gating policy is conforming when below-threshold confidence
never produces a decision, for any question type, response and
threshold. -/
def Conforming (g : QType → Response → Pct → Decision) : Prop :=
  ∀ (ty : QType) (r : Response) (τ : Pct), r.conf < τ → g ty r τ = none

/-- The conforming gate is conforming. -/
theorem gate_conforming : Conforming (fun ty r τ => gate ty τ r) := by
  intro ty r τ h
  simp only [gate]
  split
  · exfalso; exact Nat.not_le.mpr h ‹τ ≤ r.conf›
  · rfl

/-- The engine bug of basal 2.8.1, as a type: a gate that decides
for every question type except `act`/`tool`. -/
def selectiveGate (ty : QType) (r : Response) (τ : Pct) : Decision :=
  if ty = QType.act ∨ ty = QType.tool then gate ty τ r else some r.argmax

/-- A witness response: two declared options, probabilities summing to
100, top probability 50 — BELOW the 5%-target-class thresholds. -/
def tieResponse : Response :=
  { declared := ["a", "b"]
    probs := [50, 50]
    argmax := 0
    conf := 50
    k_ge_2 := by decide
    len_declared := by decide
    conf_is_top := by decide
    argmax_mem := by decide
    argmax_is_max := by
      intro j hj
      have h2 : ([50, 50] : List Pct).length = 2 := rfl
      have hjn : j < 2 := by omega
      rcases (by omega : j = 0 ∨ j = 1) with h | h
      · subst h; simp
      · subst h; simp
    probs_le_100 := by
      intro p hp
      have h1 : p = 50 ∨ p ∈ [50] := List.mem_cons.mp hp
      rcases h1 with h | h
      · subst h; decide
      · have h3 := List.mem_singleton.mp h
        subst h3; decide
    sum_100 := by decide }

/-- The selective policy is NOT conforming: `choice` decides below the
threshold with no deferral. ONE counterexample type kills the universal
claim — that is the point of typing `Conforming` by `QType`. -/
theorem selective_not_conforming : ¬ Conforming selectiveGate := by
  intro C
  have violation : selectiveGate QType.choice tieResponse 75 = none :=
    C QType.choice tieResponse 75 (by decide)
  simp only [selectiveGate] at violation
  exact absurd violation (by decide)

/-- Hard answer boundary, integer core (EVALUATION threshold, SanSi §4
metrics — not a production gating policy; see module docstring). A hard
answer is given iff the top probability reaches (1 + 1/K)/2; with `conf`
a percentage and K options, `2·K·conf ≥ 100·(K+1)`. -/
def isHard (K : Nat) (conf : Pct) : Prop := 2 * K * conf ≥ 100 * (K + 1)

/-- Pinning the boundary for binary questions: hard answer iff
confidence ≥ 75%. -/
theorem isHard_K2 (c : Nat) : isHard 2 c ↔ c ≥ 75 := by
  unfold isHard
  omega

/-- Same theorem for a `Pct`-typed confidence (definitionally the same). -/
theorem isHard_K2_pct (c : Pct) : isHard 2 c ↔ c ≥ 75 := isHard_K2 c

end TypedDecision
