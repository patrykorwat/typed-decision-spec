import TypedDecision.Defer

/-!
# QType-specific response contracts

`Response` (Basic.lean) is the COMMON core: K ≥ 2 declared options, a
normalized integer distribution over them, and a confidence equal to the
top probability. The six `QType`s, however, are not semantically
identical — this module states what each type MEANS and what the shared
contract already guarantees for it.

**Fully formal semantics (here):**
* `noul` — a binary decision: exactly two declared options — the
  YES/NO pair (`declared_pair`) — with the confidence loop carried
  explicitly (`BinaryResponse` via `noulResponseOf`); `tieBinary` shows
  the no-decision boundary is a well-formed state and
  `tieBinary_defers` that it is gating-visible.
* `multi` — **separate per-label binary distributions with update
  locality**: a LIST of independent `BinaryResponse`s, one per UNIQUE
  label (`labels_nodup`, `labels_nonempty`, `Fin`-indexed `multiSet`);
  `multi_set_independent` proves the structural half — the statistical
  half is NOT claimed (separate marginals do not determine a joint
  distribution); `gateMulti` returns a `MultiDecisionResult` keeping
  the label–decision mapping.
* `score` — **a scalar-value contract on an explicit [0, 100] scale**:
  `ScoreResponse` (value + confidence + the confidence's source loop —
  separate quantities, neither functionally determined by the other),
  `expectedValue` = floor of the exact rational EV
  (`exactEVnum`/`expectedValue_floor`/`expectedValueTruncates`),
  `scoreOfDist` (canonical path), `ScoreCalib` (own threshold + loop
  binding), `gateScore` (payload = the value; wrong loop and
  below-threshold both abstain).

**Deferred (semantics genuinely differ, documented in README):**
`act` (expected-cost actions), `tool` (agent next-step). For these only
the deferral semantics are covered by `Conforming` for every `QType`.
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

/-! ## Score: a scalar-value contract (v1.5, hardened v1.5.1) -/

theorem le100_30 : (30 : Nat) ≤ 100 := by omega
theorem le100_55 : (55 : Nat) ≤ 100 := by omega
theorem le100_85 : (85 : Nat) ≤ 100 := by omega

/-- **A score prediction**: a value on the explicit [0, 100] scale plus
a confidence in the Pct sense. THE TWO ARE SEPARATE QUANTITIES — the
value is what the model predicts on the scale, the confidence is how
certain the model is of that prediction, and neither is functionally
determined by the other (see `value_differs_from_confidence` and
`same_conf_diff_value`). `confidenceLoopIdx` records WHICH loop the
confidence came from — a calibration fitted at one loop must not be
applied to a confidence from another (mirror of `Calib.loopIdx`). -/
structure ScoreResponse where
  value : Pct
  confidence : Pct
  confidenceLoopIdx : Nat
  value_le_100 : value ≤ 100
  conf_le_100 : confidence ≤ 100

/-- Two witnesses of the score contract (confidence from loops 2 and 5). -/
def score85of55 : ScoreResponse :=
  { value := 85, confidence := 55, confidenceLoopIdx := 2,
    value_le_100 := le100_85, conf_le_100 := le100_55 }

def score30of55 : ScoreResponse :=
  { value := 30, confidence := 55, confidenceLoopIdx := 5,
    value_le_100 := le100_30, conf_le_100 := le100_55 }

/-- The value of the 85-of-55 witness. -/
theorem score85of55_value : score85of55.value = 85 := rfl
/-- The confidence of the 85-of-55 witness. -/
theorem score85of55_conf : score85of55.confidence = 55 := rfl
/-- The confidence loop of the 85-of-55 witness. -/
theorem score85of55_loop : score85of55.confidenceLoopIdx = 2 := rfl
/-- The value of the 30-of-55 witness. -/
theorem score30of55_value : score30of55.value = 30 := rfl
/-- The confidence loop of the 30-of-55 witness. -/
theorem score30of55_loop : score30of55.confidenceLoopIdx = 5 := rfl

/-- **The predicted value is not its certainty**: a well-formed score
response whose value differs from its confidence. -/
theorem value_differs_from_confidence :
    score85of55.value ≠ score85of55.confidence := by
  show (85 : Nat) ≠ 55
  omega

/-- **Confidence does not determine the value**: two well-formed score
responses with the SAME confidence and DIFFERENT values. -/
theorem same_conf_diff_value :
    score30of55.confidence = score85of55.confidence
      ∧ score30of55.value ≠ score85of55.value := by
  refine ⟨rfl, ?_⟩
  show (30 : Nat) ≠ 85
  omega

/-- **The loops differ too**: the two witnesses carry their confidence
from different loops — the loop index is independent data, not derived
from the value. -/
theorem same_conf_diff_loop :
    score30of55.confidenceLoopIdx ≠ score85of55.confidenceLoopIdx := by
  show (5 : Nat) ≠ 2
  omega

/-- The total weight of a score distribution. -/
def distSum (dist : List (Nat × Nat)) : Nat := (dist.map Prod.snd).sum

/-- **The EXACT numerator** of the expected value: Σ value·weight — the
rational expected value is `exactEVnum dist / 100` (denominator fixed
at 100), NO truncation. -/
def exactEVnum (dist : List (Nat × Nat)) : Nat :=
  (dist.map (fun p => p.1 * p.2)).sum

/-- **The integer expected value**: the FLOOR of the exact rational
expected value `exactEVnum dist / 100` (`Nat` division truncates). The
name documents the semantics — e.g. `[(0,50),(1,50)]` has exact value
1/2 and integer value 0 (`expectedValueTruncates`). -/
def expectedValue (dist : List (Nat × Nat)) : Nat :=
  exactEVnum dist / 100

/-- **The integer EV is the floor of the exact one**: `100 · EV ≤ Σ v·w`
and `Σ v·w ≤ 100 · EV + 99` — the exact rational value lies in
`[EV, EV + 1)`. -/
theorem expectedValue_floor (dist : List (Nat × Nat)) :
    100 * expectedValue dist ≤ exactEVnum dist
      ∧ exactEVnum dist ≤ 100 * expectedValue dist + 99 := by
  have hdm := Nat.div_add_mod (exactEVnum dist) 100
  have hlt := Nat.mod_lt (exactEVnum dist) (by omega : 0 < 100)
  show 100 * (exactEVnum dist / 100) ≤ exactEVnum dist
    ∧ exactEVnum dist ≤ 100 * (exactEVnum dist / 100) + 99
  omega

/-- **Truncation is real, not hypothetical**: the distribution
`[(0, 50), (1, 50)]` has exact expected value 1/2 (numerator 50) and
integer expected value 0. -/
theorem expectedValueTruncates :
    expectedValue [(0, 50), (1, 50)] = 0 ∧ exactEVnum [(0, 50), (1, 50)] = 50 := by
  constructor <;> rfl

/-- Auxiliary bound: Σ v·w ≤ 100·Σ w whenever every value is ≤ 100. -/
theorem mapPairSum_le (dist : List (Nat × Nat))
    (hvals : ∀ p ∈ dist, p.1 ≤ 100) :
    exactEVnum dist ≤ 100 * (dist.map Prod.snd).sum := by
  induction dist with
  | nil => simp [exactEVnum]
  | cons p rest ih =>
    have hmem : p ∈ p :: rest := List.mem_cons_self
    have hp := hvals p hmem
    have hmul : p.1 * p.2 ≤ 100 * p.2 := Nat.mul_le_mul_right p.2 hp
    have hrest := ih (fun q hq => hvals q (List.mem_cons_of_mem p hq))
    simp only [List.map_cons, List.sum_cons, exactEVnum] at *
    omega

/-- **The expected value stays on the scale**: for a well-formed score
distribution (every value ≤ 100, weights summing to 100), the integer
expected value is ≤ 100. -/
theorem expectedValue_le_100 (dist : List (Nat × Nat))
    (hvals : ∀ p ∈ dist, p.1 ≤ 100) (hsum : distSum dist = 100) :
    expectedValue dist ≤ 100 := by
  have hproj : (dist.map Prod.snd).sum = 100 := hsum
  have h := mapPairSum_le dist hvals
  show exactEVnum dist / 100 ≤ 100
  omega

/-- A demo: the integer expected value of `[(30, 40), (70, 60)]`
(weights 40+60) is 54 — closed computation, the definition is
executable. -/
theorem expectedValue_demo : expectedValue [(30, 40), (70, 60)] = 54 := rfl

/-- The demo distribution's values are on the scale. -/
theorem demoDist_vals : ∀ p ∈ ([(30, 40), (70, 60)]: List (Nat × Nat)), p.1 ≤ 100 := by
  intro p hp
  rcases List.mem_cons.mp hp with h | h
  · subst h; omega
  · rcases List.mem_cons.mp h with h2 | h2
    · subst h2; omega
    · exact absurd h2 (by simp)

/-- The demo distribution's weights sum to 100. -/
theorem demoDist_sum : distSum ([(30, 40), (70, 60)]: List (Nat × Nat)) = 100 := by
  show (((30, 40) :: ([(70, 60)]: List (Nat × Nat))).map Prod.snd).sum = 100
  simp

/-- The demo distribution's exact numerator. -/
theorem demoDist_exact : exactEVnum [(30, 40), (70, 60)] = 5400 := rfl

/-- **The canonical score response from a distribution**: the predicted
value IS the integer expected value of the distribution (proved on
scale); the confidence is carried separately, WITH its source loop. -/
def scoreOfDist (dist : List (Nat × Nat)) (c : Pct) (loopIdx : Nat)
    (hvals : ∀ p ∈ dist, p.1 ≤ 100) (hsum : distSum dist = 100)
    (hc : c ≤ 100) : ScoreResponse :=
  { value := expectedValue dist, confidence := c, confidenceLoopIdx := loopIdx,
    value_le_100 := expectedValue_le_100 dist hvals hsum, conf_le_100 := hc }

/-- **A score calibration is its own object** — separate from the
binary `Calib` (the score contract has its own threshold, scope and
LOOP BINDING). `threshold_le_100` is ONLY the structural scale bound —
whether τ is statistically calibrated is empirical and outside this
model (same precision as `Calib.certified` in Loop.lean). -/
structure ScoreCalib where
  τ : Pct
  threshold_le_100 : τ ≤ 100
  loopIdx : Nat

/-- **The score gate**: decide — with the predicted VALUE as payload —
iff the calibration is bound to the confidence's OWN loop AND the
confidence admits it; otherwise abstain. The payload is `r.value`,
never `r.confidence`. -/
def gateScore (c : ScoreCalib) (r : ScoreResponse) : Option Nat :=
  if c.loopIdx = r.confidenceLoopIdx ∧ c.τ ≤ r.confidence then some r.value else none

/-- **Wrong loop: the score calibration does not apply** — the gate
abstains regardless of the confidence (mirror of
`wrong_loop_never_decides`). -/
theorem gateScore_wrong_loop_never_decides (c : ScoreCalib) (r : ScoreResponse)
    (h : c.loopIdx ≠ r.confidenceLoopIdx) : gateScore c r = none := by
  simp only [gateScore]
  exact if_neg (fun hc => h hc.1)

/-- **Below the score threshold the gate abstains** (mirror of
`gate_conforming` for the score contract). -/
theorem gateScore_defers_below (c : ScoreCalib) (r : ScoreResponse)
    (h : r.confidence < c.τ) : gateScore c r = none := by
  simp only [gateScore]
  exact if_neg (fun hc => Nat.not_le.mpr h hc.2)

/-- **The payload is the predicted VALUE** — at an honest call site
(loop match) with the confidence admitting the threshold, the deciding
gate returns the value, never the confidence. -/
theorem gateScore_payload_is_value (c : ScoreCalib) (r : ScoreResponse)
    (hloop : c.loopIdx = r.confidenceLoopIdx) (hdec : c.τ ≤ r.confidence) :
    gateScore c r = some r.value := by
  simp only [gateScore]
  rw [if_pos (by exact ⟨hloop, hdec⟩)]

theorem le100_40 : (40 : Nat) ≤ 100 := by omega
theorem le100_70 : (70 : Nat) ≤ 100 := by omega

def score30of40 : ScoreResponse :=
  { value := 30, confidence := 40, confidenceLoopIdx := 2,
    value_le_100 := le100_30, conf_le_100 := le100_40 }

def score30of70 : ScoreResponse :=
  { value := 30, confidence := 70, confidenceLoopIdx := 2,
    value_le_100 := le100_30, conf_le_100 := le100_70 }

theorem score30of40_value : score30of40.value = 30 := rfl
theorem score30of40_conf : score30of40.confidence = 40 := rfl
theorem score30of70_value : score30of70.value = 30 := rfl
theorem score30of70_conf : score30of70.confidence = 70 := rfl

/-- **The same value with different confidences**: neither quantity is a
function of the other — the reverse direction of `same_conf_diff_value`
(their confidences differ AND their values agree). -/
theorem same_value_pair_differs :
    score30of40.value = score30of70.value
      ∧ score30of40.confidence ≠ score30of70.confidence := by
  refine ⟨rfl, ?_⟩
  show (40 : Nat) ≠ 70
  omega

/-- The score contract does NOT pin the value/confidence provenance
loop — it is trusted adapter metadata. This is a DECISION, recorded here
and in the README: `confidenceLoopIdx` is an annotation, not a proof of
origin (provenance would need a loop-indexed type and a controlled
constructor). -/
theorem loops_are_metadata :
    ∃ (r : ScoreResponse), r.confidence = 55 ∧ r.confidenceLoopIdx = 5 := by
  exact ⟨score30of55, rfl, rfl⟩

/-- **The score result of gating**: the payload/value pairing travels
with the result — the mirror of `MultiDecisionResult` for the scalar
contract. -/
structure ScoreDecisionResult where
  value : Option Nat
  confLoopIdx : Nat

/-- Gating with the result carrying its provenance: the loop index in
the result is the calibration's binding, so an adapter cannot lose the
conf-loop ↔ calib-loop pairing. -/
def gateScoreResult (c : ScoreCalib) (r : ScoreResponse) : ScoreDecisionResult :=
  { value := gateScore c r, confLoopIdx := r.confidenceLoopIdx }

/-- The result's payload agrees with the plain gate. -/
theorem gateScoreResult_value (c : ScoreCalib) (r : ScoreResponse) :
    (gateScoreResult c r).value = gateScore c r := rfl

/-- The result carries the response's own confidence loop. -/
theorem gateScoreResult_loop (c : ScoreCalib) (r : ScoreResponse) :
    (gateScoreResult c r).confLoopIdx = r.confidenceLoopIdx := rfl

/-- **Separate per-label quantities**: the two 30-of-x witnesses carry
the SAME value with DIFFERENT confidences (and vice versa in
`same_conf_diff_value`) — neither quantity is a function of the other. -/
theorem same_value_pair_differs2 :
    score30of40.value = score30of70.value
      ∧ score30of40.confidence ≠ score30of70.confidence :=
  same_value_pair_differs

end QTypes
