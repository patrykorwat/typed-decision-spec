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
* `act` — **the expected-cost contract**: `ActResponse` (per-action
  `CostEntry` distributions — each cost carries its own scale proof —
  computed exact numerators, `sel_min` + `sel_first` over
  `actions.idxOf`), `ActCalib` (a CONFIDENCE threshold + loop
  binding), `gateAct` (payload = the selected action; wrong loop and
  below-threshold both abstain), `ActDecisionResult` (both loop
  indices travel). The first-declared rule is exercised by the tie
  witnesses: `demoTieMin`/`demoTieFirst` (selection at index 0) and
  the NON-trivial `demoTie2Min`/`demoTie2First` (selection at index 1,
  the earlier action strictly more expensive, the later one tied) —
  `tie2_first_only` shows the later-tied selection's obligation is
  unsatisfiable, so that construction is impossible.
* `tool` — **the next-step contract**: `ToolResponse` (the selected
  next step from a declared, non-empty, duplicate-free vocabulary +
  confidence with its own loop), `ToolCalib` (a CONFIDENCE threshold +
  loop binding), `gateTool` (payload = the selected tool; wrong loop
  and below-threshold both abstain), `ToolDecisionResult` (both loop
  indices travel). Deliberately NO cost model and NO tie-break: the
  next-step choice carries no declared ordering quantity (that is
  act's job), so the vocabulary distinctness makes the selection's
  identity unambiguous — semantics genuinely differ from act, which
  selects by computed expected cost.

**Deferred:** none at the contract level; `ResponseFor` (#16) remains
the unification target.

`Conforming` (Defer.lean) is the shared gate contract for the BASE
`Response`: safe deferral below τ AND a sound argmax decision at or
above it, for every `QType` at the plain-response layer. The
specialized contracts add their own loop-bound gates (`gateScore`,
`gateAct`, `gateTool`) over their richer response types.
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
    declared_nodup := by decide
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
        declared_nodup := by decide
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
  have hC := gate_conforming
  intro x hx
  obtain ⟨d, hd, hx⟩ := List.mem_map.mp hx
  have hgate : gate QType.multi τ d.response = none :=
    hC.1 QType.multi d.response τ (hbelow d hd)
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
    gate QType.noul τ tieBinary.response = none := by
  have hC := gate_conforming
  -- tieBinary.response.conf = 50 definitionally; the hypothesis gives 50 < τ
  exact hC.1 QType.noul tieBinary.response τ (by
    have : tieBinary.response.conf = 50 := rfl
    rw [this]; exact h)

/-! ## Score: a scalar-value contract (v1.5, hardened v1.5.1) -/

theorem le100_30 : (30 : Nat) ≤ 100 := by omega
theorem le100_55 : (55 : Nat) ≤ 100 := by omega
theorem le100_85 : (85 : Nat) ≤ 100 := by omega
theorem le100_10 : (10 : Nat) ≤ 100 := by omega
theorem le100_20 : (20 : Nat) ≤ 100 := by omega
theorem le100_40 : (40 : Nat) ≤ 100 := by omega
theorem le100_70 : (70 : Nat) ≤ 100 := by omega
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

/-- **The score result of gating**: the decision plus BOTH loop indices —
the response's confidence loop AND the calibration's bound loop — so the
conf-loop ↔ calib-loop pairing travels with the result and a mismatch
becomes visible in the value itself. -/
structure ScoreDecisionResult where
  value : Option Nat
  /-- The confidence loop of the response that was gated. -/
  confLoopIdx : Nat
  /-- The loop the calibration was fitted at. -/
  calibLoopIdx : Nat

/-- Gating with the result carrying its provenance: both indices travel
with the decision — the confidence loop from the response, the
calibration loop from the calibration. -/
def gateScoreResult (c : ScoreCalib) (r : ScoreResponse) : ScoreDecisionResult :=
  { value := gateScore c r, confLoopIdx := r.confidenceLoopIdx,
    calibLoopIdx := c.loopIdx }

/-- The result's payload agrees with the plain gate. -/
theorem gateScoreResult_value (c : ScoreCalib) (r : ScoreResponse) :
    (gateScoreResult c r).value = gateScore c r := rfl

/-- The result carries the response's own confidence loop. -/
theorem gateScoreResult_loop (c : ScoreCalib) (r : ScoreResponse) :
    (gateScoreResult c r).confLoopIdx = r.confidenceLoopIdx := rfl

/-- The result carries the calibration's own loop. -/
theorem gateScoreResult_calibLoop (c : ScoreCalib) (r : ScoreResponse) :
    (gateScoreResult c r).calibLoopIdx = c.loopIdx := rfl

/-- **Classification:** `gateScoreResult` is the PUBLIC contract shape
for gating results (the pairing travels with the decision); plain
`gateScore` remains the internal helper. The README documents this. -/
theorem gateScoreResult_is_public_shape (c : ScoreCalib) (r : ScoreResponse) :
    (gateScoreResult c r).value = gateScore c r
      ∧ (gateScoreResult c r).confLoopIdx = r.confidenceLoopIdx
      ∧ (gateScoreResult c r).calibLoopIdx = c.loopIdx :=
  ⟨gateScoreResult_value c r, gateScoreResult_loop c r,
   gateScoreResult_calibLoop c r⟩

/-! ## Act: an expected-cost contract (v1.6)

**Design decisions (recorded before implementation, per the review):**

1. **Direction:** the best action MINIMIZES the exact expected cost —
   `exactCostNum`, never the floored `expectedCost` (the floor is lossy
   and can mask differences between actions).
2. **Tie-breaking:** on equal `exactCostNum`, the FIRST action in
   declaration order wins (deterministic; abstaining on ties would make
   the gate non-monotone).
3. **Costs live on their own scale** with an explicit `MAX_COST`, exact
   numerator + floor semantics like score.
4. **Confidence describes the trustworthiness of the action choice
   itself** — neither the magnitude of the cost nor the certainty of a
   single cost forecast; its measurable correctness criterion is defined
   in the evaluation data, outside this model. It stays a separate
   quantity with its own loop binding.
-/

/-- The MAX_COST of the act contract's scale. -/
def MAX_COST : Nat := 100

/-- A single cost–weight entry on the act scale: the cost CARRIES its own
scale proof (`cost_le_max`), so an out-of-scale cost is unrepresentable
at the entry level — no separate well-formedness obligation for callers. -/
structure CostEntry where
  cost : Nat
  weight : Nat
  cost_le_max : cost ≤ MAX_COST

/-- The total weight of a cost distribution. -/
def distCostSum (dist : List CostEntry) : Nat := (dist.map (fun e => e.weight)).sum

/-- **The exact cost numerator**: Σ cost·weight — the rational expected
cost is `exactCostNum dist / 100`, NO truncation. -/
def exactCostNum (dist : List CostEntry) : Nat :=
  (dist.map (fun e => e.cost * e.weight)).sum

/-- **The integer expected cost**: the FLOOR of the exact rational
expected cost `exactCostNum dist / 100` (`Nat` division truncates).
NEVER use this for selection — the floor is lossy. -/
def expectedCost (dist : List CostEntry) : Nat :=
  exactCostNum dist / 100

/-- The floor bound for costs, mirror of `expectedValue_floor`. -/
theorem expectedCost_floor (dist : List CostEntry) :
    100 * expectedCost dist ≤ exactCostNum dist
      ∧ exactCostNum dist ≤ 100 * expectedCost dist + 99 := by
  have hdm := Nat.div_add_mod (exactCostNum dist) 100
  have hlt := Nat.mod_lt (exactCostNum dist) (by omega : 0 < 100)
  show 100 * (exactCostNum dist / 100) ≤ exactCostNum dist
    ∧ exactCostNum dist ≤ 100 * (exactCostNum dist / 100) + 99
  omega

/-- **Selection by the EXACT cost, not the floor**: a concrete witness —
actions `a` (exact cost 100: distribution `[(1, 50), (1, 50)]`) and `b`
(exact cost 150: `[(3, 50), (0, 50)]`) — BOTH normalized (weights sum
to 100) — have the SAME floor `expectedCost = 1` but DIFFERENT exact
numerators (100 vs 150); selecting on the floor could not distinguish
them. The contract therefore selects on `exactCostNum`. -/
theorem floor_loses_information :
    expectedCost [⟨1, 50, by decide⟩, ⟨1, 50, by decide⟩]
      = expectedCost [⟨3, 50, by decide⟩, ⟨0, 50, by decide⟩]
      ∧ exactCostNum [⟨1, 50, by decide⟩, ⟨1, 50, by decide⟩]
        ≠ exactCostNum [⟨3, 50, by decide⟩, ⟨0, 50, by decide⟩] := by
  refine ⟨rfl, ?_⟩
  have h1 : exactCostNum [⟨1, 50, by decide⟩, ⟨1, 50, by decide⟩] = 100 := rfl
  have h2 : exactCostNum [⟨3, 50, by decide⟩, ⟨0, 50, by decide⟩] = 150 := rfl
  omega

/-- **The act response**: per-action cost distributions (each entry
CARRIES its own scale proof via `CostEntry.cost_le_max`; each
distribution with a PROVED normalized weight sum), the exact cost
numerators EQUAL to the computed map (`nums_eq_map`), the SELECTED
action which IS the minimal-exact-cost one (`sel_min` over
`actions.idxOf`) and the FIRST-DECLARED among minima (`sel_first`), a
confidence with its source loop. Well-formedness a caller could
otherwise silently violate is enforced by the type. -/
structure ActResponse where
  actions : List String
  costDists : List (List CostEntry)
  exactCostNums : List Nat
  selected : String
  confidence : Pct
  confidenceLoopIdx : Nat
  actions_nodup : actions.Nodup
  actions_nonempty : actions ≠ []
  len_match : costDists.length = actions.length
  nums_match : exactCostNums.length = actions.length
  /-- The numerators are the COMPUTED ones — "computed, never supplied"
  holds for the whole type, not just the constructor. -/
  nums_eq_map : exactCostNums = costDists.map exactCostNum
  /-- Every cost distribution's weights sum to 100 (normalized). In-scale
  costs need no separate invariant: each `CostEntry` carries its own
  `cost_le_max`. -/
  dists_normalized : ∀ x ∈ costDists, distCostSum x = 100
  /-- The selected action is a MINIMUM of the exact cost numerators
  over the actions (in order): the numerator at the selected position
  (first declared among minima) is a lower bound for every other. -/
  sel_min : ∀ i (_ : i < actions.length),
    exactCostNums[i]! ≥ exactCostNums[actions.idxOf selected]!
  /-- **First-declared among minima**: any action whose exact cost
  TIES with the selected one cannot come earlier in the declaration
  order. Together with `sel_min` this pins the first-declared
  tie-break rule. -/
  sel_first : ∀ i (_ : i < actions.length),
    exactCostNums[i]! = exactCostNums[actions.idxOf selected]! →
      i ≥ actions.idxOf selected
  sel_mem : selected ∈ actions
  conf_le_100 : confidence ≤ 100

/-- Build an act response from per-action cost distributions: the exact
cost numerators are COMPUTED (`List.map exactCostNum`), never supplied;
the caller must certify normalization, minimality AND the first-declared
rule (costs need no certificate — each `CostEntry` carries its own
scale proof). -/
def actOfDists (actions : List String) (costDists : List (List CostEntry))
    (selected : String) (c : Pct) (loopIdx : Nat)
    (hnd : actions.Nodup) (hne : actions ≠ [])
    (hlen : costDists.length = actions.length)
    (hnorm : ∀ x ∈ costDists, distCostSum x = 100)
    (hmin : ∀ i (_ : i < actions.length),
      (costDists.map exactCostNum)[i]! ≥
        (costDists.map exactCostNum)[actions.idxOf selected]!)
    (hfirst : ∀ i (_ : i < actions.length),
      (costDists.map exactCostNum)[i]! =
        (costDists.map exactCostNum)[actions.idxOf selected]! →
        i ≥ actions.idxOf selected)
    (hmem : selected ∈ actions) (hc : c ≤ 100) : ActResponse :=
  { actions := actions, costDists := costDists,
    exactCostNums := costDists.map exactCostNum,
    selected := selected, confidence := c, confidenceLoopIdx := loopIdx,
    actions_nodup := hnd, actions_nonempty := hne, len_match := hlen,
    nums_match := by rw [List.length_map]; exact hlen,
    nums_eq_map := rfl,
    dists_normalized := hnorm,
    sel_min := hmin,
    sel_first := hfirst,
    sel_mem := hmem, conf_le_100 := hc }

/-- **An act calibration is its own object**: threshold is a
CONFIDENCE threshold (`threshold_le_100`, ≤ 100 — the gate compares τ
with `r.confidence`, not with any cost), plus the loop it was fitted
at. The cost scale (`MAX_COST`) is a separate notion and is NOT bound
here. -/
structure ActCalib where
  τ : Pct
  threshold_le_100 : τ ≤ 100
  loopIdx : Nat

/-- **The act gate**: decide — with the SELECTED ACTION as payload —
iff the calibration is bound to the confidence's own loop AND the
confidence admits it; otherwise abstain. The payload is `r.selected`,
never a cost and never the confidence. -/
def gateAct (c : ActCalib) (r : ActResponse) : Option String :=
  if c.loopIdx = r.confidenceLoopIdx ∧ c.τ ≤ r.confidence then some r.selected else none

/-- **Wrong loop: the act calibration does not apply** (mirror of
`gateScore_wrong_loop_never_decides`). -/
theorem gateAct_wrong_loop_never_decides (c : ActCalib) (r : ActResponse)
    (h : c.loopIdx ≠ r.confidenceLoopIdx) : gateAct c r = none := by
  simp only [gateAct]
  exact if_neg (fun hc => h hc.1)

/-- **Below the act threshold the gate abstains** (mirror of
`gateScore_defers_below`). -/
theorem gateAct_defers_below (c : ActCalib) (r : ActResponse)
    (h : r.confidence < c.τ) : gateAct c r = none := by
  simp only [gateAct]
  exact if_neg (fun hc => Nat.not_le.mpr h hc.2)

/-- **The payload is the SELECTED ACTION** — at an honest call site the
deciding gate returns the action identifier, never a cost and never the
confidence. -/
theorem gateAct_payload_is_action (c : ActCalib) (r : ActResponse)
    (hloop : c.loopIdx = r.confidenceLoopIdx) (hdec : c.τ ≤ r.confidence) :
    gateAct c r = some r.selected := by
  simp only [gateAct]
  rw [if_pos (by exact ⟨hloop, hdec⟩)]

/-- The selected action's own index is IN bounds — the non-vacuity
guard for the `!`-indexed `sel_min`/`sel_first`: with `sel_mem` present
the `idxOf` fallback (which would index at `length` and silently yield
`0`) cannot fire. -/
theorem selected_idxOf_lt (r : ActResponse) :
    r.actions.idxOf r.selected < r.actions.length :=
  List.idxOf_lt_length_of_mem r.sel_mem

/-- **The act result of gating**: the decision plus BOTH loop indices —
the response's confidence loop AND the calibration's bound loop (mirror
of `ScoreDecisionResult`; the pairing travels with the decision). -/
structure ActDecisionResult where
  action : Option String
  /-- The confidence loop of the response that was gated. -/
  confLoopIdx : Nat
  /-- The loop the calibration was fitted at. -/
  calibLoopIdx : Nat

/-- Gating with the result carrying its provenance: both indices travel
with the decision. -/
def gateActResult (c : ActCalib) (r : ActResponse) : ActDecisionResult :=
  { action := gateAct c r, confLoopIdx := r.confidenceLoopIdx,
    calibLoopIdx := c.loopIdx }

/-- The result's payload agrees with the plain gate. -/
theorem gateActResult_action (c : ActCalib) (r : ActResponse) :
    (gateActResult c r).action = gateAct c r := rfl

/-- The result carries the response's own confidence loop. -/
theorem gateActResult_confLoop (c : ActCalib) (r : ActResponse) :
    (gateActResult c r).confLoopIdx = r.confidenceLoopIdx := rfl

/-- The result carries the calibration's own loop. -/
theorem gateActResult_calibLoop (c : ActCalib) (r : ActResponse) :
    (gateActResult c r).calibLoopIdx = c.loopIdx := rfl

/-- **Classification:** `gateActResult` is the PUBLIC contract shape for
act gating results (mirror of `gateScoreResult_is_public_shape`). -/
theorem gateActResult_is_public_shape (c : ActCalib) (r : ActResponse) :
    (gateActResult c r).action = gateAct c r
      ∧ (gateActResult c r).confLoopIdx = r.confidenceLoopIdx
      ∧ (gateActResult c r).calibLoopIdx = c.loopIdx :=
  ⟨gateActResult_action c r, gateActResult_confLoop c r,
   gateActResult_calibLoop c r⟩

/-- The demo act distributions: deploy (exact numerator 1000), rollback
(3000) and wait (2000) — each a normalized singleton on the act scale. -/
def dDeploy : List CostEntry := [⟨10, 100, le100_10⟩]
def dRollback : List CostEntry := [⟨30, 100, le100_30⟩]
def dWait : List CostEntry := [⟨20, 100, le100_20⟩]
def demoDists : List (List CostEntry) := [dDeploy, dRollback, dWait]

/-- The demo TIE distributions: TWO actions with the SAME exact numerator
3000 (`dRollback` and `dTieB`) — the first-declared one must win. -/
def dTieB : List CostEntry := [⟨30, 100, le100_30⟩]
def tieDists : List (List CostEntry) := [dRollback, dTieB]

/-- The demo distributions are normalized (weights sum to 100). -/
theorem demoNorm : ∀ x ∈ demoDists, distCostSum x = 100 := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h; rfl
  · rcases List.mem_cons.mp h with h2 | h2
    · subst h2; rfl
    · rcases List.mem_cons.mp h2 with h3 | h3
      · subst h3; rfl
      · exact absurd h3 (by simp)

/-- The demo selection satisfies the minimality invariant (deploy at
index 0 has exact cost 1000, the minimum of 1000/3000/2000). -/
theorem demoSel_min3 :
    ∀ i (_ : i < List.length (["deploy", "rollback", "wait"] : List String)),
      (demoDists.map exactCostNum)[i]! ≥
        (demoDists.map exactCostNum)[List.idxOf "deploy"
          (["deploy", "rollback", "wait"] : List String)]! := by
  intro i hi
  have hi3 : i < 3 := by simp at hi; omega
  have hidx : List.idxOf "deploy" (["deploy", "rollback", "wait"] : List String) = 0 := by
    simp
  rw [hidx]
  match i with
  | 0 => exact Nat.le_refl _
  | 1 => show (3000 : Nat) ≥ 1000; omega
  | 2 => show (2000 : Nat) ≥ 1000; omega
  | n + 3 => omega

/-- The demo selection is FIRST-DECLARED among minima: `deploy` sits at
index 0, so any action tying with it cannot come earlier. -/
theorem demoSel_first3 :
    ∀ i (_ : i < List.length (["deploy", "rollback", "wait"] : List String)),
      (demoDists.map exactCostNum)[i]! =
        (demoDists.map exactCostNum)[List.idxOf "deploy"
          (["deploy", "rollback", "wait"] : List String)]! →
        i ≥ List.idxOf "deploy" (["deploy", "rollback", "wait"] : List String) := by
  intro i _ _
  have h0 : List.idxOf "deploy" (["deploy", "rollback", "wait"] : List String) = 0 := by
    simp
  omega

/-- The demo tie distributions are normalized (weights sum to 100). -/
theorem demoTieNorm : ∀ x ∈ tieDists, distCostSum x = 100 := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h; rfl
  · rcases List.mem_cons.mp h with h2 | h2
    · subst h2; rfl
    · exact absurd h2 (by simp)

/-- The tie selection satisfies minimality trivially: BOTH numerators are
3000, so the first-declared (`rollback`, index 0) is a minimum. -/
theorem demoTieMin :
    ∀ i (_ : i < List.length (["rollback", "wait"] : List String)),
      (tieDists.map exactCostNum)[i]! ≥
        (tieDists.map exactCostNum)[List.idxOf "rollback"
          (["rollback", "wait"] : List String)]! := by
  intro i hi
  have hi2 : i < 2 := by simp at hi; omega
  have hidx : List.idxOf "rollback" (["rollback", "wait"] : List String) = 0 := by
    simp
  rw [hidx]
  match i with
  | 0 => exact Nat.le_refl _
  | 1 => show (3000 : Nat) ≥ 3000; omega
  | n + 2 => omega

/-- The tie selection is FIRST-DECLARED among minima: `rollback` sits at
index 0, so any action tying with it cannot come earlier. -/
theorem demoTieFirst :
    ∀ i (_ : i < List.length (["rollback", "wait"] : List String)),
      (tieDists.map exactCostNum)[i]! =
        (tieDists.map exactCostNum)[List.idxOf "rollback"
          (["rollback", "wait"] : List String)]! →
        i ≥ List.idxOf "rollback" (["rollback", "wait"] : List String) := by
  intro i _ _
  have h0 : List.idxOf "rollback" (["rollback", "wait"] : List String) = 0 := by
    simp
  omega

/-! ### The NON-trivial tie witness (review round 2)

`demoTieMin`/`demoTieFirst` hold the selection at index 0, where
`sel_first` reduces to `i ≥ 0`. The witness below puts the selection at
INDEX 1 with the earlier action STRICTLY more expensive (4000 > 3000)
and the later one tied (3000 = 3000) — the first case where `sel_first`
has real content. `tie2_first_only` proves the later-tied selection's
`sel_first` obligation UNSATISFIABLE; since `actOfDists` takes that
obligation as a hypothesis, `selected := "wait"` is unbuildable for
this collection. -/

/-- A 4000-cost singleton (exact numerator 40·100) on the act scale. -/
def d4000 : List CostEntry := [⟨40, 100, le100_40⟩]

/-- The NON-trivial tie collection: `[4000, 3000, 3000]` — the minimum
sits at index 1, an earlier action is more expensive, a later one ties. -/
def tie2Dists : List (List CostEntry) := [d4000, dRollback, dTieB]

/-- The tie2 distributions are normalized (weights sum to 100). -/
theorem demoTie2Norm : ∀ x ∈ tie2Dists, distCostSum x = 100 := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · subst h; rfl
  · rcases List.mem_cons.mp h with h2 | h2
    · subst h2; rfl
    · rcases List.mem_cons.mp h2 with h3 | h3
      · subst h3; rfl
      · exact absurd h3 (by simp)

/-- The tie2 selection satisfies minimality: `rollback` (index 1) has
exact cost 3000 — the earlier `deploy` (4000) is strictly more
expensive, the later `wait` ties. -/
theorem demoTie2Min :
    ∀ i (_ : i < List.length (["deploy", "rollback", "wait"] : List String)),
      (tie2Dists.map exactCostNum)[i]! ≥
        (tie2Dists.map exactCostNum)[List.idxOf "rollback"
          (["deploy", "rollback", "wait"] : List String)]! := by
  have hnum : ∀ j (_ : j < 3), (tie2Dists.map exactCostNum)[j]! ≥ 3000 := by
    intro j hj
    have h0 : (tie2Dists.map exactCostNum)[0]! = 4000 := rfl
    have h1 : (tie2Dists.map exactCostNum)[1]! = 3000 := rfl
    have h2 : (tie2Dists.map exactCostNum)[2]! = 3000 := rfl
    by_cases e0 : j = 0
    · subst e0; omega
    · by_cases e1 : j = 1
      · subst e1; omega
      · have e2 : j = 2 := by omega
        subst e2; omega
  intro i hi
  have hidx : List.idxOf "rollback" (["deploy", "rollback", "wait"] : List String) = 1 := by
    decide
  rw [hidx]
  exact hnum i hi

/-- The tie2 selection is FIRST-DECLARED among minima: `rollback` sits
at index 1; the case `i = 0` is refuted NUMERICALLY (4000 ≠ 3000), not
vacuously. -/
theorem demoTie2First :
    ∀ i (_ : i < List.length (["deploy", "rollback", "wait"] : List String)),
      (tie2Dists.map exactCostNum)[i]! =
        (tie2Dists.map exactCostNum)[List.idxOf "rollback"
          (["deploy", "rollback", "wait"] : List String)]! →
        i ≥ List.idxOf "rollback" (["deploy", "rollback", "wait"] : List String) := by
  intro i hi Heq
  have hidx : List.idxOf "rollback" (["deploy", "rollback", "wait"] : List String) = 1 := by
    decide
  rw [hidx] at Heq
  have h0 : (tie2Dists.map exactCostNum)[0]! = 4000 := rfl
  by_cases e0 : i = 0
  · subst e0
    rw [h0] at Heq
    have h1 : (tie2Dists.map exactCostNum)[1]! = 3000 := rfl
    rw [h1] at Heq
    omega
  · omega

/-- **The later-tied selection's obligation is UNSATISFIABLE**: for
`selected := "wait"` (index 2) the `sel_first` statement fails at
`i = 1` (3000 = 3000 but 1 < 2). Since `actOfDists` takes `hfirst` as
a hypothesis, an act response over `tie2Dists` selecting `wait` cannot
be constructed. -/
theorem tie2_first_only :
    ¬ (∀ i (_ : i < List.length (["deploy", "rollback", "wait"] : List String)),
        (tie2Dists.map exactCostNum)[i]! =
          (tie2Dists.map exactCostNum)[List.idxOf "wait"
            (["deploy", "rollback", "wait"] : List String)]! →
          i ≥ List.idxOf "wait" (["deploy", "rollback", "wait"] : List String)) := by
  intro H
  have hidx : List.idxOf "wait" (["deploy", "rollback", "wait"] : List String) = 2 := by
    decide
  have h1 := H 1 (by decide)
  rw [hidx] at h1
  have hant : (tie2Dists.map exactCostNum)[1]! = (tie2Dists.map exactCostNum)[2]! := by
    rw [show (tie2Dists.map exactCostNum)[1]! = 3000 from rfl,
        show (tie2Dists.map exactCostNum)[2]! = 3000 from rfl]
  have := h1 hant
  omega

/-- Constructibility, positive side: the response over `tie2Dists`
selecting `rollback` (index 1) EXISTS — the certificates discharge. -/
def tie2Resp : ActResponse :=
  actOfDists ["deploy", "rollback", "wait"] tie2Dists "rollback" 100 2
    (by decide) (by decide) (by decide)
    demoTie2Norm demoTie2Min demoTie2First (by simp) (by decide)

/-! ## Tool: the next-step contract (v1.7)

**Design decisions (recorded before implementation, per the review):**

1. **Selection from a declared vocabulary** — `tools` non-empty and
   duplicate-free, `selected ∈ tools`: the chosen next step is a member
   of the declared list (mirror of `ActResponse.actions`, WITHOUT the
   cost machinery — the next-step choice carries no declared ordering
   quantity; act is the cost-bearing sibling).
2. **No tie-break rule** — without a cost (or any ordering quantity)
   the first-declared question does not arise; the vocabulary
   distinctness makes the selection's identity unambiguous.
3. **Confidence** describes the trustworthiness of the next-step choice
   itself — neither a cost magnitude nor a per-forecast certainty; its
   measurable correctness criterion lives in evaluation data, outside
   this model (mirror of act; the README fixes the scoring definition).
4. **Gate** — `ToolCalib` is a CONFIDENCE threshold (`threshold_le_100`,
   ≤ 100) plus the loop it was fitted at; `gateTool` decides with the
   SELECTED TOOL as payload, abstains below the threshold and on a
   wrong loop (mirror of `gateAct`).
5. **Result shape** — `ToolDecisionResult` carries BOTH loop indices
   (mirror of `ScoreDecisionResult`/`ActDecisionResult`); the pairing
   travels with the decision.

-/

/-- **A tool response**: the selected next step from a declared
vocabulary (non-empty, duplicate-free) with a confidence describing the
trustworthiness of the choice itself, and the confidence's own source
loop. -/
structure ToolResponse where
  tools : List String
  selected : String
  confidence : Pct
  confidenceLoopIdx : Nat
  /-- The vocabulary entries are distinct. -/
  tools_nodup : tools.Nodup
  /-- A next-step question has at least one candidate step. -/
  tools_nonempty : tools ≠ []
  /-- The selected tool is a member of the declared vocabulary. -/
  sel_mem : selected ∈ tools
  conf_le_100 : confidence ≤ 100

/-- The canonical constructor: the caller certifies vocabulary
well-formedness, membership and the confidence bound. -/
def toolOf (tools : List String) (selected : String) (c : Pct) (loopIdx : Nat)
    (hnd : tools.Nodup) (hne : tools ≠ [])
    (hmem : selected ∈ tools) (hc : c ≤ 100) : ToolResponse :=
  { tools := tools, selected := selected, confidence := c,
    confidenceLoopIdx := loopIdx,
    tools_nodup := hnd, tools_nonempty := hne,
    sel_mem := hmem, conf_le_100 := hc }

/-- The selected tool's own index is IN bounds — the non-vacuity guard
for `!`-indexed selection arguments (mirror of the act guard). -/
theorem tool_selected_idxOf_lt (r : ToolResponse) :
    r.tools.idxOf r.selected < r.tools.length :=
  List.idxOf_lt_length_of_mem r.sel_mem

/-- **A tool calibration**: a CONFIDENCE threshold (`threshold_le_100`,
≤ 100 — the gate compares τ with `r.confidence`) plus the loop it was
fitted at. -/
structure ToolCalib where
  τ : Pct
  threshold_le_100 : τ ≤ 100
  loopIdx : Nat

/-- **The tool gate**: decide — with the SELECTED TOOL as payload —
iff the calibration is bound to the confidence's own loop AND the
confidence admits it; otherwise abstain. The payload is `r.selected`,
never the confidence. -/
def gateTool (c : ToolCalib) (r : ToolResponse) : Option String :=
  if c.loopIdx = r.confidenceLoopIdx ∧ c.τ ≤ r.confidence then some r.selected else none

/-- **Wrong loop: the tool calibration does not apply** (mirror of
`gateAct_wrong_loop_never_decides`). -/
theorem gateTool_wrong_loop_never_decides (c : ToolCalib) (r : ToolResponse)
    (h : c.loopIdx ≠ r.confidenceLoopIdx) : gateTool c r = none := by
  simp only [gateTool]
  exact if_neg (fun hc => h hc.1)

/-- **Below the tool threshold the gate abstains** (mirror of
`gateAct_defers_below`). -/
theorem gateTool_defers_below (c : ToolCalib) (r : ToolResponse)
    (h : r.confidence < c.τ) : gateTool c r = none := by
  simp only [gateTool]
  exact if_neg (fun hc => Nat.not_le.mpr h hc.2)

/-- **The payload is the SELECTED TOOL** — at an honest call site the
deciding gate returns the tool identifier, never the confidence. -/
theorem gateTool_payload_is_tool (c : ToolCalib) (r : ToolResponse)
    (hloop : c.loopIdx = r.confidenceLoopIdx) (hdec : c.τ ≤ r.confidence) :
    gateTool c r = some r.selected := by
  simp only [gateTool]
  rw [if_pos (by exact ⟨hloop, hdec⟩)]

/-- **The tool result of gating**: the decision plus BOTH loop indices —
the response's confidence loop AND the calibration's bound loop (mirror
of `ActDecisionResult`). -/
structure ToolDecisionResult where
  selected : Option String
  /-- The confidence loop of the response that was gated. -/
  confLoopIdx : Nat
  /-- The loop the calibration was fitted at. -/
  calibLoopIdx : Nat

/-- Gating with the result carrying its provenance: both indices travel
with the decision. -/
def gateToolResult (c : ToolCalib) (r : ToolResponse) : ToolDecisionResult :=
  { selected := gateTool c r, confLoopIdx := r.confidenceLoopIdx,
    calibLoopIdx := c.loopIdx }

/-- The result's payload agrees with the plain gate. -/
theorem gateToolResult_selected (c : ToolCalib) (r : ToolResponse) :
    (gateToolResult c r).selected = gateTool c r := rfl

/-- The result carries the response's own confidence loop. -/
theorem gateToolResult_confLoop (c : ToolCalib) (r : ToolResponse) :
    (gateToolResult c r).confLoopIdx = r.confidenceLoopIdx := rfl

/-- The result carries the calibration's own loop. -/
theorem gateToolResult_calibLoop (c : ToolCalib) (r : ToolResponse) :
    (gateToolResult c r).calibLoopIdx = c.loopIdx := rfl

/-- **Classification:** `gateToolResult` is the PUBLIC contract shape
for tool gating results (mirror of `gateActResult_is_public_shape`). -/
theorem gateToolResult_is_public_shape (c : ToolCalib) (r : ToolResponse) :
    (gateToolResult c r).selected = gateTool c r
      ∧ (gateToolResult c r).confLoopIdx = r.confidenceLoopIdx
      ∧ (gateToolResult c r).calibLoopIdx = c.loopIdx :=
  ⟨gateToolResult_selected c r, gateToolResult_confLoop c r,
   gateToolResult_calibLoop c r⟩

/-- The demo tool vocabulary: three DISTINCT next steps; the selection
`read` sits at a non-trivial index (1). -/
def demoTools : List String := ["search", "read", "write"]

/-- The demo tool responses: vocabulary membership and distinctness are
the only obligations; the confidence comes from the readout. -/
def demoToolResp : ToolResponse :=
  toolOf demoTools "read" 20 5 (by decide) (by decide) (by simp [demoTools]) (by decide)

def demoToolRespPos : ToolResponse :=
  toolOf demoTools "read" 84 2 (by decide) (by decide) (by simp [demoTools]) (by decide)

def demoToolRespBnd : ToolResponse :=
  toolOf demoTools "read" 100 2 (by decide) (by decide) (by simp [demoTools]) (by decide)

end QTypes
