import TypedDecision.Defer

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
options carrying the YES/NO pair (the formal binary contract), with the
distribution and confidence as in the shared core. -/
structure BinaryResponse where
  response : Response
  declared_len_2 : response.declared.length = 2
  /-- The two declared options ARE the formal YES and NO (in this
  order) — the contract is a decision between them, not between two
  arbitrary strings. -/
  declared_pair : response.declared = ["YES", "NO"]

/-- Multi-label: independent binary decisions, one per UNIQUE label.
Each label carries its OWN normalized distribution — the multi response
is NOT one distribution over the power set (which would be 2^k options
and destroy the independence reading). -/
structure MultiResponse where
  labels : List String
  decisions : List BinaryResponse
  len_match : decisions.length = labels.length
  /-- Labels are unique — `["positive", "positive"]` is not a
  well-formed multi response (the per-label reading collapses). -/
  labels_nodup : labels.Nodup

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
    { declared := ["YES", "NO"]
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
  { response := default, declared_len_2 := rfl, declared_pair := rfl }

instance : Inhabited BinaryResponse where
  default := tieBinary

instance : Inhabited MultiResponse where
  default := { labels := ["l1"], decisions := [default], len_match := rfl,
               labels_nodup := by simp }

/-- **Independence of labels** (the formal content of "multi"): setting
label i's decision leaves every OTHER label's stored decision untouched
(observed at position j, `?`-form). This is **update locality** —
the structural half of independence. The statistical half (the labels'
distributions do not constrain each other) is carried by the per-label
`BinaryResponse` objects, not by one joint distribution. -/
theorem multi_set_independent (m : MultiResponse) (d : BinaryResponse)
    (i : Nat) (j : Nat) (hne : i ≠ j) :
    (m.decisions.set i d)[j]? = m.decisions[j]? :=
  List.getElem?_set_ne (l := m.decisions) (i := i) (j := j) (a := d) hne

/-- **Label–decision binding:** position i of `decisions` is the decision
FOR label i — the lengths agree, so indexing by the label's position is
the same act on both lists. -/
theorem multi_len_match (m : MultiResponse) :
    m.decisions.length = m.labels.length := m.len_match

/-! ## Gating the collection (issue: Multi decision gating) -/

/-- Gating a whole `MultiResponse`: the shared `gate` applied to every
label's binary response at the collection's own threshold. Each label's
decision is computed from ITS OWN response — the collection-level gate
is the pointwise lift, no joint machinery. -/
def gateMulti (τ : Pct) (m : MultiResponse) : List (Option Nat) :=
  m.decisions.map (fun d => TypedDecision.gate QType.multi τ d.response)

/-- **Length agreement:** the gated collection has exactly as many
decisions as labels (mirror of `len_match` through `map`). -/
theorem gateMulti_length (τ : Pct) (m : MultiResponse) :
    (gateMulti τ m).length = m.labels.length := by
  simp only [gateMulti, List.length_map]
  exact m.len_match

/-- **Per-label deferral:** below the threshold, EVERY label defers —
the collection never decides partially (mirror of `gate_conforming`
lifted through `map`). -/
theorem gateMulti_defers_below (τ : Pct) (m : MultiResponse)
    (hbelow : ∀ d ∈ m.decisions, d.response.conf < τ) :
    ∀ x ∈ gateMulti τ m, x = none := by
  intro x hx
  obtain ⟨d, hd, hx⟩ := List.mem_map.mp hx
  have hgate : gate QType.multi τ d.response = none := by
    refine gate_conforming QType.multi d.response τ ?_
    exact hbelow d hd
  rw [hx] at hgate
  exact hgate

/-- Update one label's decision, keeping the structure well-formed (the
record-update notation does NOT re-prove `len_match`, so this explicit
constructor is the canonical update). -/
def multiSet (m : MultiResponse) (d : BinaryResponse) (i : Nat) : MultiResponse :=
  { labels := m.labels, decisions := m.decisions.set i d,
    len_match := by rw [List.length_set]; exact m.len_match,
    labels_nodup := m.labels_nodup }

theorem multiSet_decisions (m : MultiResponse) (d : BinaryResponse) (i : Nat) :
    (multiSet m d i).decisions = m.decisions.set i d := rfl

/-- **Update locality for the gated collection:** updating label i's
decision changes only position i of the gated list (pointwise
consequence of `multi_set_independent` through `map`). -/
theorem gateMulti_set_independent (m : MultiResponse) (d : BinaryResponse)
    (τ : Pct) (i : Nat) (j : Nat) (hj : j < m.decisions.length) (hne : i ≠ j) :
    (gateMulti τ (multiSet m d i))[j]?
      = (gateMulti τ m)[j]? := by
  rw [show gateMulti τ (multiSet m d i)
          = (multiSet m d i).decisions.map (fun x => gate QType.multi τ x.response) from rfl,
      multiSet_decisions,
      show gateMulti τ m = m.decisions.map (fun x => gate QType.multi τ x.response) from rfl]
  have hL : ((m.decisions.set i d).map (fun x => gate QType.multi τ x.response))[j]?
      = Option.map (fun x => gate QType.multi τ x.response) ((m.decisions.set i d)[j]?) := by
    rw [List.getElem?_map (f := fun x => gate QType.multi τ x.response) (l := m.decisions.set i d)]
  have hR : (m.decisions.map (fun x => gate QType.multi τ x.response))[j]?
      = Option.map (fun x => gate QType.multi τ x.response) (m.decisions[j]?) := by
    rw [List.getElem?_map (f := fun x => gate QType.multi τ x.response) (l := m.decisions)]
  rw [hL, hR, multi_set_independent m d i j hne]

/-! ## The noul tie state and its abstention -/

/-- **The tie state defers:** at any threshold ABOVE 50, the 50/50
binary response produces NO decision — the unresolvable state is a
gating-visible state, not just a well-formed response (mirror of
`gate_conforming` at `conf = 50 < τ`). -/
theorem tieBinary_defers (τ : Pct) (h : 50 < τ) :
    gate QType.noul τ tieBinary.response = none :=
  gate_conforming QType.noul tieBinary.response τ (by
    -- tieBinary.response.conf = 50 definitionally; the hypothesis gives 50 < τ
    have : tieBinary.response.conf = 50 := rfl
    rw [this]; exact h)

end QTypes
