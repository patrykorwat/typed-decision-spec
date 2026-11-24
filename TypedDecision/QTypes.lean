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
Each label carries its OWN **separate per-label binary distribution**
(the marginals do not determine a joint distribution — the module does
NOT claim statistical independence, only separate per-label objects
with update locality) — the multi response is NOT one distribution over
the power set (which would be 2^k options and destroy the per-label
reading). A multi question has AT LEAST ONE label — the empty collection
is not a question (and makes `Fin` vacuous). -/
structure MultiResponse where
  labels : List String
  decisions : List BinaryResponse
  len_match : decisions.length = labels.length
  /-- Labels are unique — `["positive", "positive"]` is not a
  well-formed multi response (the per-label reading collapses). -/
  labels_nodup : labels.Nodup
  /-- At least one label: a multi question with no labels is not a
  question (and `Fin m.labels.length` would be vacuous). -/
  labels_nonempty : labels ≠ []

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

/-- Every entry of the binary distribution `[p, 100 - p]` is ≤ 100. -/
theorem respP_le (p : Nat) (hp : p ≤ 100) : ∀ x ∈ [p, 100 - p], x ≤ 100 := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · omega
  · rcases List.mem_cons.mp h with h2 | h2
    · omega
    · exact absurd h2 (by simp)

/-- The binary distribution sums to 100. -/
theorem respP_sum (p : Nat) (hp : p ≤ 100) : [p, 100 - p].sum = 100 := by
  simp only [List.sum_cons, List.sum_nil]
  omega

/-- The `noul` boundary: the 50/50 tie — a well-formed binary response
("no decision possible" is a semantic state, not a model failure).
Named constructor (no global `Inhabited Response` instance — the shared
type must not default to one QType's semantics). -/
def tieResponse : Response :=
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
binary response. -/
def tieBinary : BinaryResponse :=
  { response := tieResponse, declared_len_2 := rfl, declared_pair := rfl }

instance : Inhabited BinaryResponse where
  default := tieBinary

instance : Inhabited MultiResponse where
  default := { labels := ["l1"], decisions := [default], len_match := rfl,
               labels_nodup := by simp, labels_nonempty := by simp }

/-- The `noul` constructor from one probability `p ≤ 100`: declared
YES/NO, probs `[p, 100-p]`, conf = max p (100-p), argmax = 0 iff p ≥ 50.
Every shared `Response` invariant holds from `hp : p ≤ 100` alone — the
binary contract is constructible for every valid readout (the Python
adapter and the multi export build their label decisions from this). -/
def noulResponseOf (p : Nat) (hp : p ≤ 100) : BinaryResponse :=
  { response :=
      { declared := ["YES", "NO"]
        probs := [p, 100 - p]
        argmax := if 50 ≤ p then 0 else 1
        conf := max p (100 - p)
        k_ge_2 := by decide
        len_declared := rfl
        conf_is_top := by
          by_cases h50 : 50 ≤ p
          · rw [if_pos h50]; exact Nat.max_eq_left (by omega)
          · rw [if_neg (by omega)]; exact Nat.max_eq_right (by omega)
        argmax_mem := by
          by_cases h50 : 50 ≤ p
          · rw [if_pos h50]; simp
          · have hl : ["YES", "NO"].length = 2 := rfl
            rw [if_neg (by omega), hl]; omega
        argmax_is_max := by
          intro j hj
          have hl : [p, 100 - p].length = 2 := rfl
          have hjn : j < 2 := by rw [hl] at hj; exact hj
          have hj0 : j = 0 ∨ j = 1 := by omega
          rcases hj0 with h | h
          · subst h; exact Nat.le_max_left p (100 - p)
          · subst h; exact Nat.le_max_right p (100 - p)
        probs_le_100 := respP_le p hp
        sum_100 := respP_sum p hp }
    declared_len_2 := rfl
    declared_pair := rfl }

/-- **Update locality of labels** (the structural half of per-label
independence): setting label i's decision leaves every OTHER label's
stored decision untouched (observed at position j, `?`-form). The
statistical half is NOT claimed: separate marginals do not determine a
joint distribution. -/
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

/-- The result of gating a whole collection: the label–decision mapping
travels WITH the result (an adapter cannot lose the pairing by
zipping). -/
structure MultiDecisionResult where
  labels : List String
  decisions : List (Option Nat)
  len_match : decisions.length = labels.length

/-- Gating a whole `MultiResponse`: the shared `gate` applied to every
label's binary response at the collection's own threshold. Each label's
decision is computed from ITS OWN response — the collection-level gate
is the pointwise lift, no joint machinery. -/
def gateMulti (τ : Pct) (m : MultiResponse) : MultiDecisionResult :=
  { labels := m.labels
    decisions := m.decisions.map (fun d => gate QType.multi τ d.response)
    len_match := by rw [List.length_map]; exact m.len_match }

/-- **Length agreement:** the gated collection has exactly as many
decisions as labels (mirror of `len_match` through `map`). -/
theorem gateMulti_length (τ : Pct) (m : MultiResponse) :
    (gateMulti τ m).decisions.length = m.labels.length := by
  show ((m.decisions.map (fun d => gate QType.multi τ d.response))).length = m.labels.length
  rw [List.length_map]
  exact m.len_match

/-- **Per-label deferral:** below the threshold, EVERY label defers —
the collection never decides partially (mirror of `gate_conforming`
lifted through `map`). -/
theorem gateMulti_defers_below (τ : Pct) (m : MultiResponse)
    (hbelow : ∀ d ∈ m.decisions, d.response.conf < τ) :
    ∀ x ∈ (gateMulti τ m).decisions, x = none := by
  intro x hx
  obtain ⟨d, hd, hx⟩ := List.mem_map.mp hx
  have hgate : gate QType.multi τ d.response = none := by
    refine gate_conforming QType.multi d.response τ ?_
    exact hbelow d hd
  rw [hx] at hgate
  exact hgate

/-- Update one label's decision, keeping the structure well-formed (the
record-update notation does NOT re-prove `len_match`, so this explicit
constructor is the canonical update). The index is a `Fin` over the
label list — pointing at a non-existent label is unrepresentable. -/
def multiSet (m : MultiResponse) (d : BinaryResponse) (i : Fin m.labels.length) :
    MultiResponse :=
  { labels := m.labels, decisions := m.decisions.set i.val d,
    len_match := by rw [List.length_set]; exact m.len_match,
    labels_nodup := m.labels_nodup, labels_nonempty := m.labels_nonempty }

theorem multiSet_decisions (m : MultiResponse) (d : BinaryResponse) (i : Fin m.labels.length) :
    (multiSet m d i).decisions = m.decisions.set i.val d := rfl

/-- **Update locality for the gated collection:** updating label i's
decision changes only position i of the gated result (pointwise
consequence of `multi_set_independent` through `map`). -/
theorem gateMulti_set_independent (m : MultiResponse) (d : BinaryResponse)
    (τ : Pct) (i : Fin m.labels.length) (j : Fin m.labels.length) (hne : i.val ≠ j.val) :
    (gateMulti τ (multiSet m d i)).decisions[j.val]?
      = (gateMulti τ m).decisions[j.val]? := by
  have hL : ((m.decisions.set i.val d).map (fun x => gate QType.multi τ x.response))[j.val]?
      = Option.map (fun x => gate QType.multi τ x.response) ((m.decisions.set i.val d)[j.val]?) := by
    rw [List.getElem?_map (f := fun x => gate QType.multi τ x.response) (l := m.decisions.set i.val d)]
  have hR : (m.decisions.map (fun x => gate QType.multi τ x.response))[j.val]?
      = Option.map (fun x => gate QType.multi τ x.response) (m.decisions[j.val]?) := by
    rw [List.getElem?_map (f := fun x => gate QType.multi τ x.response) (l := m.decisions)]
  show (gateMulti τ (multiSet m d i)).decisions[j.val]?
      = (gateMulti τ m).decisions[j.val]?
  rw [show (gateMulti τ (multiSet m d i)).decisions
          = (m.decisions.set i.val d).map (fun x => gate QType.multi τ x.response) from rfl,
      show (gateMulti τ m).decisions
          = m.decisions.map (fun x => gate QType.multi τ x.response) from rfl,
      hL, hR, multi_set_independent m d i.val j.val hne]

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
