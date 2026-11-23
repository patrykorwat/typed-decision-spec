/-!
# Typed decision contract: responses

A typed decision engine receives a state, a question and K ≥ 2 declared
options and returns one probability per declared option in a single
forward pass, without generating text (basal 2.x contract; SanSi §3:
"a typed decision is a call with ... K≥2 declared options. The model
returns a distribution p ∈ Δ^K over the options and no text").

The response is bound to the DECLARED options: `declared` is carried in
the structure, so a response pointing outside the caller's options is
not constructible. Domain constraints on `Pct` live here (each entry
≤ 100, entries sum to 100 — the integer core of `p ∈ Δ^K`).
-/

namespace TypedDecision

/-- Probability of one option, integer percentage. Bounded and
normalized on `Response` (a `Fin 101` bound on a single entry would
still leave the distribution unnormalized). `abbrev` (not `def`): the
elaborator sees through it, so `omega` works on Pct-typed terms. -/
abbrev Pct := Nat

/-- Sum of a list is at most its length times the list's maximum. -/
theorem sum_le_top : ∀ (ps : List Nat) (c : Nat),
    (∀ j, j < ps.length → ps[j]! ≤ c) → ps.sum ≤ ps.length * c
  | [], _ => by simp
  | p :: ps, c => by
      intro h
      have h0 : p ≤ c := by
        have h9 := h 0 (by simp)
        simpa using h9
      have hrest : ∀ j, j < ps.length → ps[j]! ≤ c := by
        intro j hj
        have h9 := h (j + 1) (by simp only [List.length_cons]; omega)
        simpa using h9
      have h10 := sum_le_top ps c hrest
      simp only [List.sum_cons, List.length_cons, Nat.add_mul]
      omega

/-- A response for a question with declared options `declared` (K ≥ 2).
`probs` is the integer core of a distribution on the declared options:
same length as `declared`, every entry ≤ 100, entries sum to 100.
`conf` is the confidence and equals the probability of `argmax`, which
is a maximiser (basal API.md: responses carry per-question calibrated
`probabilities` and `confidence` — probability of the chosen answer). -/
structure Response where
  declared : List String
  probs : List Pct
  argmax : Nat
  conf : Pct
  k_ge_2 : 2 ≤ declared.length
  len_declared : probs.length = declared.length
  conf_is_top : conf = probs[argmax]!
  argmax_mem : argmax < declared.length
  argmax_is_max : ∀ j (_ : j < probs.length), probs[j]! ≤ conf
  probs_le_100 : ∀ p ∈ probs, p ≤ 100
  sum_100 : probs.sum = 100

/-- Every reported probability is at most the confidence
(the confidence is the TOP probability). -/
theorem conf_ge_all (r : Response) : ∀ i (_ : i < r.probs.length), r.probs[i]! ≤ r.conf :=
  r.argmax_is_max

/-- The argmax indexes a DECLARED option: answers can never fall outside
the options the caller gave (README: "the answer can never fall outside
the options you gave"). Because `declared` is part of the structure,
a response pointing outside it cannot be constructed. -/
theorem answer_inside_options (r : Response) : r.argmax < r.declared.length :=
  r.argmax_mem

/-- Normalization forces the top probability to at least 100/K
(pigeonhole: the entries sum to 100 and none exceeds `conf`). -/
theorem top_ge_100_over_K (r : Response) : 100 ≤ r.probs.length * r.conf := by
  have h : r.probs.sum ≤ r.probs.length * r.conf :=
    sum_le_top r.probs r.conf r.argmax_is_max
  have h2 := r.sum_100
  rw [← h2]
  exact h

end TypedDecision
