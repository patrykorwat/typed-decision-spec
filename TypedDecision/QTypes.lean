import TypedDecision.Basic

/-!
# QType-specific response contracts

`Response` (Basic.lean) is the COMMON core: K ≥ 2 declared options, a
normalized integer distribution over them, and a confidence equal to the
top probability. The six `QType`s, however, are not semantically
identical — this module states what each type MEANS and what the shared
contract already guarantees for it.

**Fully formal semantics (here):**
* `noul` — a binary decision: exactly two declared options (witness
  `BinaryResponse`); `tieBinary` shows the no-decision boundary is a
  well-formed state.
* `multi` — independent binary decisions over labels: a LIST of
  independent `BinaryResponse`s, one per label (`MultiResponse`);
  `multi_set_independent` is the formal content of independence —
  updating one label's decision leaves every other label untouched
  (as observed at position j, `?`-form to stay decision-free).

**Shared-property-only types (documented, not yet fully formal):**
`choice` (pick one of K options — this IS the shared `Response`),
`score` (a value on a scale — needs a scale type), `act` (an action —
needs an action vocabulary), `tool` (a next step — needs a tool
vocabulary). For these only the confidence-gating properties
(`conf_is_top`, `probs_le_100`, `sum_100`, `Conforming`) are proved; the
README presents them as such until dedicated contracts land.
-/

namespace QTypes

open TypedDecision

/-- A binary decision: the `noul` instance — exactly two declared
options (the formal yes/no pair), distribution and confidence as in
the shared core. -/
structure BinaryResponse where
  response : Response
  declared_len_2 : response.declared.length = 2

/-- Multi-label: independent binary decisions, one per label. Each label
carries its OWN normalized distribution — the multi response is NOT one
distribution over the power set (which would be 2^k options and destroy
the independence reading). -/
structure MultiResponse where
  labels : List String
  decisions : List BinaryResponse
  len_match : decisions.length = labels.length

theorem resp50_le : ∀ j (_ : j < ([50, 50] : List Nat).length), [50, 50][j]! ≤ 50 := by
  intro j hj
  have h2 : [50, 50][j]! = 50 := by
    match j with
    | 0 => rfl
    | 1 => rfl
    | n + 2 => simp at hj; omega
  rw [h2]
  omega

theorem resp50_mem : ∀ p ∈ ([50, 50] : List Nat), p ≤ 100 := by
  intro p hp
  have h2 : p = 50 := by
    rcases List.mem_cons.mp hp with h | h
    · omega
    · rcases List.mem_cons.mp h with h2 | h2
      · omega
      · exact absurd h2 (by simp)
  omega

instance : Inhabited Response where
  default :=
    { declared := ["a", "b"]
      probs := [50, 50]
      argmax := 0
      conf := 50
      k_ge_2 := by decide
      len_declared := rfl
      conf_is_top := rfl
      argmax_mem := by decide
      argmax_is_max := resp50_le
      probs_le_100 := resp50_mem
      sum_100 := by simp }

/-- The `noul` boundary is reachable: the 50/50 tie is a well-formed
binary response ("no decision possible" is a semantic state, not a
model failure). -/
def tieBinary : BinaryResponse :=
  { response := default, declared_len_2 := rfl }

instance : Inhabited BinaryResponse where
  default := tieBinary

instance : Inhabited MultiResponse where
  default := { labels := ["l1"], decisions := [default], len_match := rfl }

/-- **Independence of labels** (the formal content of "multi"): setting
label i's decision leaves every OTHER label's stored decision untouched
(observed at position j, `?`-form). Labels are updated one at a time,
without constraining each other — there is no joint distribution over
the power set. -/
theorem multi_set_independent (m : MultiResponse) (d : BinaryResponse)
    (i : Nat) (j : Nat) (hne : i ≠ j) :
    (m.decisions.set i d)[j]? = m.decisions[j]? :=
  List.getElem?_set_ne (l := m.decisions) (i := i) (j := j) (a := d) hne

end QTypes
