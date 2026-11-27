import TypedDecision.Defer

/-!
# Typed decision contract: looped engines (System 1.5)

Pins the loop semantics of a SanSi-style engine (arXiv 2610.07730 §3):
one stack applied T times, readout after every loop (per-loop head:
W+U_tV_t, τ_t), input tokens encoded ONCE. Machine-checked properties:

* `runBin_length` / `budget_at` — one run delivers every budget 1..T,
  and budget t's confidence sits at INDEX t-1 of the trace (exact
  position, not mere membership);
* `binConf_sound` — every trace entry IS the confidence of a
  CONSTRUCTED `Response` (the readout feeds a real normalized binary
  distribution), so the trace cannot carry numbers impossible for the
  declared response shape;
* `reinjection_differs` — re-injecting tokens each loop is a
  DIFFERENT model: a witness over the ACTUAL engines (`reinjectedRun`
  vs `runBin`) with a valid `Readout`; the re-injected number is not
  even a confidence of a constructed response;
* `wrong_loop_never_decides` / `no_calib_never_decides` — a calibration
  applies only at its own loop index; without a calibration record the
  engine refuses (SanSi §5.3: ECE best at loop 3, climbing again by
  loop 8 — calibration is bound to the loop it was fitted at).

The per-loop readout is a `Readout`: a function of the loop index AND
the hidden state, bounded by construction — misassigned heads are
detectable. The loop layer is a BINARY reference model for Tier-1: the
readout yields one `Pct` per loop, so every response built here is a
2-option distribution (`binResponseOf`); multi-class readouts (K ≥ 2
per loop) are the `ResponseFor` generalization, deliberately deferred.

Scope note (recorded): `Calib.loopIdx` and `LoopResponse.loopIdx` are
UNBOUNDED `Nat` — trusted adapter metadata, not a proof of origin
(the index-typed structure would be the full-strength variant; the
raw `LoopResponse.mk` stays public on purpose).
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

/-- A per-loop readout: depends on the loop index AND the hidden state,
bounded by construction (so a normalized distribution can be built
from it). -/
structure Readout where
  f : Nat → Nat → Pct
  bounded : ∀ t h, f t h ≤ 100

/-- conf = probs[argmax]! for the binary shape, as a standalone lemma. -/
theorem binConf_is_top (p : Nat) (hp : p ≤ 100) :
    max p (100 - p) = [p, 100 - p][if 50 ≤ p then 0 else 1]! := by
  by_cases h50 : 50 ≤ p
  · have hmax : max p (100 - p) = p := Nat.max_eq_left (by omega)
    rw [hmax, if_pos h50]
    rfl
  · have hmax : max p (100 - p) = 100 - p := Nat.max_eq_right (by omega)
    rw [hmax, if_neg (by omega)]
    rfl

/-- probs[j]! ≤ conf for the binary shape, as a standalone lemma. -/
theorem binConf_is_max (p : Nat) (hp : p ≤ 100) (j : Nat) (hj : j < [p, 100 - p].length) :
    [p, 100 - p][j]! ≤ max p (100 - p) := by
  have h2 : [p, 100 - p].length = 2 := rfl
  have hjn : j < 2 := by omega
  rcases j with _ | j
  · simpa using Nat.le_max_left p (100 - p)
  · have : j = 0 := by omega
    subst this
    simpa using Nat.le_max_right p (100 - p)

/-- All binary probs are ≤ 100, standalone. -/
theorem binProbs_le_100 (p : Nat) (hp : p ≤ 100) : ∀ x ∈ [p, 100 - p], x ≤ 100 := by
  intro x hx
  rcases List.mem_cons.mp hx with h | h
  · omega
  · rcases List.mem_cons.mp h with h2 | h2
    · omega
    · exact absurd h2 (by simp)

/-- The binary probs sum to 100, standalone. -/
theorem binProbs_sum (p : Nat) (hp : p ≤ 100) : [p, 100 - p].sum = 100 := by
  have hsub : p + (100 - p) = 100 := by omega
  simp only [List.sum_cons, List.sum_nil]
  omega

/-- The binary distribution as a named export: `binProbsOf p hp = [p, 100-p]`.
This is the shape the frozen vectors' `probs_trace` compares (the full
per-loop distribution, not only the confidence). -/
def binProbsOf (p : Nat) (hp : p ≤ 100) : List Pct := [p, 100 - p]

/-- The exported distribution is a length-2 list summing to 100. -/
theorem binProbsOf_sound (p : Nat) (hp : p ≤ 100) :
    (binProbsOf p hp).length = 2 ∧ (binProbsOf p hp).sum = 100 := by
  constructor
  · simp [binProbsOf]
  · exact binProbs_sum p hp

/-- A binary response from one probability p (≤ 100): probs [p, 100-p],
conf = max p (100-p), argmax = 0 iff p ≥ 50. Constructed so every
`Response` invariant holds from `hp : p ≤ 100` alone. `p` is `Nat`
(Pct is a reducible alias; Nat-typed binders keep omega usable). -/
def binResponseOf (p : Nat) (hp : p ≤ 100) : Response :=
  { declared := ["a", "b"]
    probs := [p, 100 - p]
    argmax := if 50 ≤ p then 0 else 1
    conf := max p (100 - p)
    k_ge_2 := by decide
    declared_nodup := by decide
    len_declared := rfl
    conf_is_top := binConf_is_top p hp
    argmax_mem := by
      by_cases h50 : 50 ≤ p
      · simp [h50]
      · simp only [if_neg (by omega)]
        simp
    argmax_is_max := by
      intro j hj
      exact binConf_is_max p hp j hj
    probs_le_100 := binProbs_le_100 p hp
    sum_100 := binProbs_sum p hp }

/-- The confidence of a binary response from p. -/
def binConfOf (p : Nat) (hp : p ≤ 100) : Pct := (binResponseOf p hp).conf

/-- The confidence IS max p (100-p), by projection of the structure. -/
theorem binConfOf_eq (p : Nat) (hp : p ≤ 100) : binConfOf p hp = max p (100 - p) := rfl

/-- The constructed response's distribution IS the standalone export
(the trace and the Response contract agree by construction). -/
theorem binResponseOf_probs (p : Nat) (hp : p ≤ 100) :
    (binResponseOf p hp).probs = binProbsOf p hp := rfl

/-- A binary response from loop t's state: the per-loop readout produces
p, the response is CONSTRUCTED from it (the trace confidence and the
Response contract are connected by construction). -/
def binResponse (r : Readout) (F : Nat → Nat) (h0 : Nat) (t : Nat) : Response :=
  binResponseOf (r.f t (iter F t h0)) (r.bounded t (iter F t h0))

/-- Loop t's confidence, derived from the constructed response. -/
def binConf (r : Readout) (F : Nat → Nat) (h0 : Nat) (t : Nat) : Pct :=
  (binResponse r F h0 t).conf

/-- One run with T loops yields the readouts for budgets 1..T
(SanSi §3: h_t = N(F(h_{t-1})), t = 1..T). The initial h_0 is the
token encoding, not a readout after a loop, so it is not an entry. -/
def runBin (F : Nat → Nat) (r : Readout) (h0 : Nat) (T : Nat) : List Pct :=
  (List.range T).map (fun i => binConf r F h0 (i + 1))

theorem runBin_length (F : Nat → Nat) (r : Readout) (h0 T : Nat) :
    (runBin F r h0 T).length = T := by
  simp [runBin, List.length_map, List.length_range]

/-- Budget t's confidence sits at index t-1 of the trace — the exact
position a consumer must use, not mere membership. -/
theorem budget_at (F : Nat → Nat) (r : Readout) (h0 T : Nat) :
    ∀ i < T, (runBin F r h0 T)[i]? = some (binConf r F h0 (i + 1)) := by
  intro i hi
  have hr : runBin F r h0 T = (List.range T).map (fun t => binConf r F h0 (t + 1)) := rfl
  rw [hr, List.getElem?_map]
  have h1 : (List.range T)[i]? = some i := List.getElem?_range hi
  rw [h1]
  rfl

/-- 50 ≤ max p (100-p) for p ≤ 100 — standalone (omega fails on this
goal shape inside structure instances; black-box the helper). Verified
against the alternative derivation from `top_ge_100_over_K`: that route
needs the SAME max-atom case analysis, so the dedicated helper stays. -/
theorem max_sub_ge (p : Nat) (hp : p ≤ 100) : 50 ≤ max p (100 - p) := by
  rcases Nat.le_total p (100 - p) with h | h
  · rw [Nat.max_eq_right h]
    omega
  · rw [Nat.max_eq_left h]
    omega

/-- Soundness of the binary confidence: within 0..100 AND ≥ 50 —
a number impossible for a normalized binary response cannot enter the
trace (P1-1). -/
theorem binConf_sound (p : Nat) (hp : p ≤ 100) :
    50 ≤ binConfOf p hp ∧ binConfOf p hp ≤ 100 := by
  rw [binConfOf_eq]
  exact ⟨max_sub_ge p hp, Nat.max_le.mpr ⟨hp, by omega⟩⟩

/-- Direct soundness of the trace confidence (review P2): for every loop
`t`, `binConf` sits in [50, 100] — no separate proof needed per consumer,
it is `binConfOf_sound` at the loop's own readout. -/
theorem binConf_loop_sound (r : Readout) (F : Nat → Nat) (h0 : Nat) (t : Nat) :
    50 ≤ binConf r F h0 t ∧ binConf r F h0 t ≤ 100 :=
  binConf_sound (r.f t (iter F t h0)) (r.bounded t (iter F t h0))

/-- Analogous bound for the elements of `runBin` (review P2): budget t's
confidence — at its exact index t-1 — is a valid confidence. -/
theorem runBin_sound (F : Nat → Nat) (r : Readout) (h0 T : Nat) :
    ∀ i < T, 50 ≤ (runBin F r h0 T)[i]! ∧ (runBin F r h0 T)[i]! ≤ 100 := by
  intro i hi
  have hb := budget_at F r h0 T i hi
  have hv : (runBin F r h0 T)[i]! = binConf r F h0 (i + 1) := by
    rw [List.getElem!_eq_getElem?_getD, hb]
    simp
  rw [hv]
  exact binConf_loop_sound r F h0 (i + 1)

/-- The WRONG engine: re-injects the token encoding at every loop
(hₜ₊₁ = F hₜ + tokens). A different model; from the outside — typed
responses only — the divergence is invisible until calibrated
numbers drift. -/
def reinjectedRun (F : Nat → Nat) (tokens : Nat) (read : Nat → Nat → Pct)
    (h0 : Nat) (T : Nat) : List Pct :=
  (List.range T).map (fun i => read (i + 1) (iter (fun h => F h + tokens) (i + 1) h0))

/-- A deliberate divergence, demonstrated on the ACTUAL engines: with
dynamics `h ↦ h + 1`, the identity readout wrapped as a valid `Readout`
and token mark 1, the re-injecting engine's RAW trace differs from the
conforming one at loop 1 (`[2]` vs `[99]` — the re-injected number is
not even a confidence of a constructed response). The witness removes
the old `confAt` helper: it calls `reinjectedRun`/`runBin` themselves. -/
theorem reinjection_differs :
    ∃ (F : Nat → Nat) (r : Readout) (h0 : Nat),
      reinjectedRun F 1 r.f h0 1 ≠ runBin F r h0 1 := by
  refine ⟨fun h => h + 1, ⟨fun _ h => h % 100, fun _ h => Nat.le_of_lt (Nat.mod_lt h (by omega))⟩,
    0, ?_⟩
  have h1 : reinjectedRun (fun h => h + 1) 1 (fun _ h => h % 100) 0 1 = [2] := rfl
  have h2 : runBin (fun h => h + 1)
      ⟨fun _ h => h % 100, fun _ h => Nat.le_of_lt (Nat.mod_lt h (by omega))⟩ 0 1 = [99] := rfl
  rw [h1, h2]
  decide

/-- The witness engines of the reinjection divergence (shared by both
witnesses): dynamics `h ↦ h + 1`, the bounded identity readout, mark 1. -/
def FWit : Nat → Nat := fun h => h + 1
def rWit : Readout := ⟨fun _ h => h % 100, fun _ h => Nat.le_of_lt (Nat.mod_lt h (by omega))⟩

/-- The SAME divergence, both sides through ONE transformation: the
re-injected state is fed through `binConfOf` (the same `max p (100-p)`
confidence construction as `runBin` uses), so the difference comes from
the state update alone, not from comparing a raw readout with a
confidence. Same dynamics/readout/mark as `reinjection_differs`:
confidence 98 (re-injected) vs 99 (conforming). -/
theorem reinjection_conf_differs :
    ∃ (F : Nat → Nat) (r : Readout) (h0 : Nat),
      binConfOf (r.f 1 (iter (fun h => F h + 1) 1 h0)) (r.bounded 1 (iter (fun h => F h + 1) 1 h0))
        ≠ binConf r F h0 1 :=
  ⟨FWit, rWit, 0, by
    have hA : binConfOf (rWit.f 1 (iter (fun h => FWit h + 1) 1 0))
        (rWit.bounded 1 (iter (fun h => FWit h + 1) 1 0)) = 98 := rfl
    have hB : binConf rWit FWit 0 1 = 99 := rfl
    show (98 : Nat) ≠ 99
    omega⟩

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

/-- Wrong question type: the calibration does not apply (mirror of the
wrong-loop refusal — the conjunctive condition has TWO guards, both
proved). -/
theorem wrong_type_never_decides (c : Calib) (ty : QType) (t : Nat) (r : Response)
    (h : c.qtype ≠ ty) : gateCalib c ty t r = none := by
  simp only [gateCalib]
  exact if_neg (fun hc => h hc.1)

/-- Below the calibration's own threshold: no decision (the bound call
site falls through to `gate`, which defers by `gate_conforming`). -/
theorem gateCalib_defers_below (c : Calib) (ty : QType) (t : Nat) (r : Response)
    (h : r.conf < c.τ) : gateCalib c ty t r = none := by
  have hC := gate_conforming
  simp only [gateCalib]
  by_cases hcond : c.qtype = ty ∧ c.loopIdx = t
  · rw [if_pos hcond]
    exact hC.1 ty r c.τ h
  · rw [if_neg hcond]

/-- The deciding path: at the calibration's OWN type and loop, with
confidence at or above τ, the gate decides with the argmax as payload. -/
theorem gateCalib_decides (c : Calib) (ty : QType) (t : Nat) (r : Response)
    (hty : c.qtype = ty) (hloop : c.loopIdx = t) (hdec : c.τ ≤ r.conf) :
    gateCalib c ty t r = some r.argmax := by
  simp only [gateCalib]
  rw [if_pos ⟨hty, hloop⟩]
  simp only [gate, gateP, decide_eq_true_eq]
  rw [if_pos hdec]

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

/-! ## The response bound to its loop (review P1-4) -/

/-- A response bound to its question type and loop index: the index
travels WITH the response, so a gate can no longer be fed a response
from loop 8 while the caller claims `t = 3` — the mismatch is visible
in the value itself. -/
structure LoopResponse where
  qtype : QType
  loopIdx : Nat
  response : Response

/-- Construct the bound response for loop t from the per-loop readout.
This is the CANONICAL constructor: `binLoopResponse_loopIdx` and
`binLoopResponse_response` pin that the stored index is the true loop
of the stored response. (The raw `LoopResponse.mk` remains public, so a
caller CAN still mislabel — provenance is guaranteed on this path, not
type-theoretically; a private ctor / index-typed structure would be the
full-strength version.) -/
def binLoopResponse (r : Readout) (F : Nat → Nat) (h0 : Nat) (t : Nat) (q : QType) :
    LoopResponse :=
  ⟨q, t, binResponse r F h0 t⟩

/-- Provenance of the canonical path, part 1: the stored index IS the
construction loop. -/
theorem binLoopResponse_loopIdx (r : Readout) (F : Nat → Nat) (h0 : Nat) (t : Nat)
    (q : QType) : (binLoopResponse r F h0 t q).loopIdx = t := rfl

/-- Provenance of the canonical path, part 2: the stored response IS the
loop's own constructed response. -/
theorem binLoopResponse_response (r : Readout) (F : Nat → Nat) (h0 : Nat) (t : Nat)
    (q : QType) : (binLoopResponse r F h0 t q).response = binResponse r F h0 t := rfl

/-- The structure-bound gate: the index is read from the response, not
from a separate caller argument. -/
def gateLoop (c : Calib) (lr : LoopResponse) : Decision :=
  if c.qtype = lr.qtype ∧ c.loopIdx = lr.loopIdx then gate lr.qtype c.τ lr.response else none

/-- Structural twin of `wrong_loop_never_decides`: a calibration cannot
decide on a response whose OWN loop index differs. -/
theorem wrong_loop_structural (c : Calib) (lr : LoopResponse)
    (h : c.loopIdx ≠ lr.loopIdx) : gateLoop c lr = none := by
  simp only [gateLoop]
  exact if_neg (fun hc => h hc.2)

/-- Structural twin of `wrong_type_never_decides`: a calibration cannot
decide on a response of a DIFFERENT question type. -/
theorem wrong_type_structural (c : Calib) (lr : LoopResponse)
    (h : c.qtype ≠ lr.qtype) : gateLoop c lr = none := by
  simp only [gateLoop]
  exact if_neg (fun hc => h hc.1)

/-- Structural twin of `gateCalib_defers_below`: the response's own
confidence below the calibration's τ — no decision. -/
theorem gateLoop_defers_below (c : Calib) (lr : LoopResponse)
    (h : lr.response.conf < c.τ) : gateLoop c lr = none := by
  have hC := gate_conforming
  simp only [gateLoop]
  by_cases hcond : c.qtype = lr.qtype ∧ c.loopIdx = lr.loopIdx
  · rw [if_pos hcond]
    exact hC.1 lr.qtype lr.response c.τ h
  · rw [if_neg hcond]

/-- Structural twin of `gateCalib_decides`: own type, own loop, at or
above τ — the gate decides with the argmax as payload. -/
theorem gateLoop_decides (c : Calib) (lr : LoopResponse)
    (hty : c.qtype = lr.qtype) (hloop : c.loopIdx = lr.loopIdx)
    (hdec : c.τ ≤ lr.response.conf) :
    gateLoop c lr = some lr.response.argmax := by
  simp only [gateLoop]
  rw [if_pos ⟨hty, hloop⟩]
  simp only [gate, gateP, decide_eq_true_eq]
  rw [if_pos hdec]

/-- The no-calibration refusal, structural layer: without a calibration
record the bound response is never decided. -/
def gateOptLoop (c : Option Calib) (lr : LoopResponse) : Decision :=
  match c with
  | some c => gateLoop c lr
  | none => none

theorem no_calib_structural_never_decides (lr : LoopResponse) :
    gateOptLoop none lr = none := by
  simp [gateOptLoop]

/-- `gateLoop` agrees with `gateCalib` whenever the passed index IS the
response's own index — the two APIs coincide at honest call sites.
Definitional: both unfold to the same `if`. -/
theorem gateLoop_eq_gateCalib (c : Calib) (lr : LoopResponse) :
    gateLoop c lr = gateCalib c lr.qtype lr.loopIdx lr.response := rfl

end TypedDecision
