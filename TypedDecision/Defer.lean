import TypedDecision.Basic

/-!
# Typed decision contract: confidence gating and deferral

Pins the escalation semantics. The normative content is `Conforming`:
BELOW the certified threshold, a gate returns NO decision (`none`).
This is the property the basal 2.8.1 engine violated for `choice`,
`noul`, `score` and `multi`: `max_error` was accepted in the payload
and silently ignored (verified 2026-11: zero deferred, answers below
the certified threshold went through) — only `act`/`tool` gated.

The hard-answer boundary mirrors SanSi §4 metrics: an unanswerable
item is right when the model gives no hard answer, i.e. its top
probability is below (1 + 1/K)/2. Here in the integer percentage core.
-/

namespace TypedDecision

/-- The engine's answer to one question: either the chosen option index,
or no decision. -/
@[reducible] def Decision := Option Nat

/-- Question types of the contract. -/
inductive QType
  | act | tool | choice | noul | score | multi
  deriving DecidableEq, Repr

/-- The conforming gate: decide only at or above the threshold. -/
def gate (τ : Pct) (r : Response) : Decision :=
  if τ ≤ r.conf then some r.argmax else none

/-- A gating policy is conforming when below-threshold confidence
never produces a decision — for EVERY question type. -/
def Conforming (g : Response → Pct → Decision) : Prop :=
  ∀ (r : Response) (τ : Pct), r.conf < τ → g r τ = none

/-- The conforming gate is conforming. -/
theorem gate_conforming : Conforming (fun (r : Response) (τ : Pct) => gate τ r) := by
  intro r τ h
  simp only [gate]
  split
  · exfalso; exact Nat.not_le.mpr h ‹τ ≤ r.conf›
  · rfl

/-- The engine bug of basal 2.8.1, as a type: a gate that decides
for every question type except `act`/`tool`. -/
def ungatedGate (ty : QType) (τ : Pct) (r : Response) : Decision :=
  if ty = QType.act ∨ ty = QType.tool then gate τ r else some r.argmax

/-- A witness response with confidence 0. -/
def zeroResponse : Response :=
  { probs := [0], argmax := 0, conf := 0
    len := by simp
    conf_is_top := by simp
    argmax_mem := by simp
    argmax_is_max := by
      intro j _
      rcases j with _ | j <;> simp }

/-- The ungated policy is NOT conforming: below-threshold answers go
through with no deferral. This is exactly the class of the verified
2.8.1 finding. -/
theorem ungated_not_conforming (ty : QType)
    (h : ty ≠ QType.act ∧ ty ≠ QType.tool) :
    ¬ Conforming (fun (r : Response) (τ : Pct) => ungatedGate ty τ r) := by
  intro C
  have violation : ungatedGate ty 1 zeroResponse = none :=
    C zeroResponse 1 (by decide)
  simp only [ungatedGate] at violation
  split at violation
  · have hc : ty = QType.act ∨ ty = QType.tool := by assumption
    rcases hc with h1 | h2
    · exact h.1 h1
    · exact h.2 h2
  · exact Option.some_ne_none _ violation

/-- Hard answer boundary, integer core: a hard answer is given iff the
top probability reaches (1 + 1/K)/2. With `conf` a percentage and K
options (K ≥ 1), that is `2·K·conf ≥ 100·(K+1)`. -/
def isHard (K : Nat) (conf : Pct) : Prop := 2 * K * conf ≥ 100 * (K + 1)

/-- Pinning the boundary for binary questions: hard answer iff
confidence ≥ 75%. -/
theorem isHard_K2 (c : Nat) : isHard 2 c ↔ c ≥ 75 := by
  unfold isHard
  omega

/-- Same theorem for a `Pct`-typed confidence (definitionally the same). -/
theorem isHard_K2_pct (c : Pct) : isHard 2 c ↔ c ≥ 75 := isHard_K2 c

end TypedDecision
