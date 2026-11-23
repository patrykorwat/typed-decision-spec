/-!
# Typed decision contract: responses

A typed decision engine receives a state, a question and K ≥ 2 declared
options and returns one probability per declared option in a single
forward pass, without generating text (basal 2.x contract; SanSi §3:
"a typed decision is a call with ... K≥2 declared options. The model
returns a distribution p ∈ Δ^K over the options and no text").

This file pins the response-side contract: the confidence is the top
probability, every probability is nonnegative (they are percentages by
construction) and the argmax is a maximiser.
-/

namespace TypedDecision

/-- Probability of one option, as an integer percentage 0..100
(the integer core; calibration files are stored as decimals, the
contract is pinned on the integers). -/
@[reducible] def Pct := Nat

/-- A response for K declared options. `probs.length = K` is the caller's
declared option count; `conf` is the confidence and by contract equals
the probability of the returned `argmax`, which is a maximiser of the
vector (basal API.md: responses carry per-question `probabilities`
calibrated and `confidence` — probability of the chosen answer). -/
structure Response where
  probs : List Pct
  argmax : Nat
  conf : Pct
  len : probs.length > 0
  conf_is_top : conf = probs[argmax]!
  argmax_mem : argmax < probs.length
  argmax_is_max : ∀ j (_ : j < probs.length), probs[j]! ≤ conf

/-- Every reported probability is at most the confidence
(the confidence is the TOP probability). -/
theorem conf_ge_all (r : Response) : ∀ i (_ : i < r.probs.length), r.probs[i]! ≤ r.conf :=
  r.argmax_is_max

/-- The argmax index points at an existing option: answers can never fall
outside the declared options (README: "the answer can never fall outside
the options you gave"). Indexing `probs[argmax]!` is total by `argmax_mem`;
the option NAME exists because the list has the declared length. -/
theorem answer_inside_options (r : Response) : r.argmax < r.probs.length :=
  r.argmax_mem

end TypedDecision
