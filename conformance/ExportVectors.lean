import TypedDecision.Loop
import TypedDecision.QTypes

open TypedDecision QTypes

/-!
# Executable conformance export (the formal half of the bridge)

Computes the Tier-1 expected values FROM the spec's definitions —
`runBin` (not a re-derived map), `isHard` via its Decidable instance
(not a duplicated formula), the shared `gateP` predicate, and the
pinned `spec_T` (a CLI T different from spec_T is REJECTED, so the
frozen budget cannot drift silently).

v1.3 additions (review round 9): the FULL response distributions
(`probs_trace`, per loop, from the constructed `Response` — by
`binResponseOf_probs` these ARE `binProbsOf`), the four exported
`gateCalib` cases, the `gateOptCalib none` case, and the
`LoopResponse` wrong-loop case (the index travels with the response).

Usage (from the repo root):
  lake env lean --run conformance/ExportVectors.lean A B M W R H0 TAU

The readout is per-loop: read t h = (W*h + R*t) % 100 — the loop index
participates, so misassigned heads are detectable (P1-4).

Prints one JSON object on stdout.
-/

open TypedDecision

def parseNat (s : String) : Nat := s.toNat!

/-- Serialize a `Decision` (`Option Nat`) the way the Python mirror
speaks: `"argmax"` for `some _`, `"none"` for `none`. -/
def decStr (d : Decision) : String :=
  match d with | some _ => "argmax" | none => "none"

def main (args : List String) : IO UInt32 := do
  match args with
  | [a, b, m, w, r, h0, tau] =>
    let A := parseNat a
    let B := parseNat b
    let M := parseNat m
    let W := parseNat w
    let R := parseNat r
    let H0 := parseNat h0
    let TAU := parseNat tau
    -- the CLI carries no T: the spec's spec_T is the single source
    let F : Nat → Nat := fun h => (A * h + B) % M
    let rd : Nat → Nat → Pct := fun t h => (W * h + R * t) % 100
    -- bounded by construction: x % 100 ≤ 99 < 100
    have hmod : ∀ x : Nat, x % 100 ≤ 100 := fun x => Nat.le_of_lt (Nat.mod_lt x (by omega))
    let read : Readout := ⟨rd, fun t h => hmod (W * h + R * t)⟩
    -- budgets 1..T, straight from `runBin`
    let trace := runBin F read H0 spec_T
    -- the reinjected counterengine, same tokens = h0
    let reinj := reinjectedRun F H0 rd H0 spec_T
    -- eval boundary (isHard, K = 2) on the DEFINITION, and the shared
    -- gate predicate at TAU
    let hard := trace.map (fun c => decide (isHard 2 c))
    let gates := trace.map (fun c => if gateP TAU c then "argmax" else "none")
    -- the FULL per-loop distributions, from the constructed Response
    -- (by binResponseOf_probs these equal binProbsOf at the loop's own
    -- readout — the trace and the export cannot disagree)
    let probs := (List.range spec_T).map
      (fun i => (binResponse read F H0 (i + 1)).probs)
    -- the exported calibration cases. τ₀ = the pin's calibration
    -- threshold; τ₁ = τ₀ - 1; τ₂ = conf(8) - 1. calib₃ (loop 3) covers
    -- applicability; calib₅ (loop 5) and calib_d (loop 3) cover the
    -- DECIDING path and the wrong-loop regression at a threshold that
    -- would decide were the index ignored.
    let tau0 := min TAU 100
    have hcert0 : tau0 ≤ 100 := Nat.min_le_right TAU 100
    let tau1 := min (TAU - 1) 100
    have hcert1 : tau1 ≤ 100 := Nat.min_le_right (TAU - 1) 100
    let conf8 := binConf read F H0 8
    let tau2 := min (conf8 - 1) 100
    have hcert2 : tau2 ≤ 100 := Nat.min_le_right (conf8 - 1) 100
    let calib3 : Calib := ⟨QType.choice, tau0, 3, hcert0⟩
    let calib5 : Calib := ⟨QType.choice, tau1, 5, hcert1⟩
    let calibD : Calib := ⟨QType.choice, tau2, 3, hcert2⟩
    let resp3 := binResponse read F H0 3
    let resp5 := binResponse read F H0 5
    let resp8 := binResponse read F H0 8
    -- cases: [own-loop per τ₀, wrong loop per τ₀, wrong QType, no calib,
    --         own-loop DECIDING (τ₁ at loop 5), wrong loop, τ₂ WOULD decide]
    let gc1 := decStr (gateCalib calib3 QType.choice 3 resp3)
    let gc2 := decStr (gateCalib calib3 QType.choice 8 resp8)
    let gc3 := decStr (gateCalib calib3 QType.act 3 resp3)
    let gc4 := decStr (gateOptCalib none QType.choice 3 resp3)
    let gc5 := decStr (gateCalib calib5 QType.choice 5 resp5)
    let gc6 := decStr (gateCalib calibD QType.choice 8 resp8)
    let gcCases := toString (List.map (fun s => "\"" ++ s ++ "\"") [gc1, gc2, gc3, gc4, gc5, gc6])
    -- the LoopResponse case: the index comes from the RESPONSE (loop 8),
    -- and the threshold is the index-ISOLATING one (conf8 - 1): a gateLoop
    -- that ignored lr.loopIdx would return argmax here — wrong_loop_structural
    let lr8 : LoopResponse := binLoopResponse read F H0 8 QType.choice
    let lrCase := decStr (gateLoop calibD lr8)
    -- the MULTI collection: 3 labels with DIFFERENT per-label distributions
    -- (label i's decision is noulResponseOf at the loop-(i+1) readout —
    -- confs 68/84/64 at loops 1/2/3 ⇒ mixed gating at τ₀: none/argmax/none)
    let mk (da db dc : BinaryResponse) : MultiResponse :=
      { labels := ["alpha", "beta", "gamma"], decisions := [da, db, dc],
        len_match := rfl, labels_nodup := by decide, labels_nonempty := by decide }
    let d1 := noulResponseOf (rd 1 (iter F 1 H0)) (hmod _)
    let d2 := noulResponseOf (rd 2 (iter F 2 H0)) (hmod _)
    let d3 := noulResponseOf (rd 3 (iter F 3 H0)) (hmod _)
    let m0 := mk d1 d2 d3
    -- update label 2 (index 1) with the loop-4 readout: others unchanged
    -- (the CANONICAL constructor multiSet; the index proof: the labels of
    -- the collection ARE the literal list, `decide` closes 1 < 3)
    let d4 := noulResponseOf (rd 4 (iter F 4 H0)) (hmod _)
    let mU := multiSet m0 d4 ⟨1, by
      have h : (mk d1 d2 d3).labels = ["alpha", "beta", "gamma"] := rfl
      rw [h]; decide⟩
    let mConfs := (m0.decisions.map (fun d => d.response.conf)).toString
    let mProbs := (m0.decisions.map (fun d => d.response.probs)).toString
    let mGates := ((gateMulti TAU m0).decisions.map
      (fun d => match d with | some _ => "\"argmax\"" | none => "\"none\"")).toString
    let mGatesU := ((gateMulti TAU mU).decisions.map
      (fun d => match d with | some _ => "\"argmax\"" | none => "\"none\"")).toString
    let mLabelsU := (["alpha", "beta", "gamma"].map (fun s => "\"" ++ s ++ "\"")).toString
    -- the ACT responses, CONSTRUCTED via actOfDists (the caller must
    -- discharge hnorm/hmin/hfirst — the tie-break is a PROVED obligation,
    -- not prose); confidences carry the readout's own ≤100 proof (hmod)
    let actResp := actOfDists ["deploy", "rollback", "wait"] demoDists "deploy"
      (rd 5 (iter F 5 H0)) 5 (by decide) (by decide) (by decide)
      demoNorm demoSel_min3 demoSel_first3 (by simp) (hmod _)
    let actRespPos := actOfDists ["deploy", "rollback", "wait"] demoDists "deploy"
      (rd 2 (iter F 2 H0)) 2 (by decide) (by decide) (by decide)
      demoNorm demoSel_min3 demoSel_first3 (by simp) (hmod _)
    let actRespTie := actOfDists ["rollback", "wait"] tieDists "rollback"
      (rd 2 (iter F 2 H0)) 2 (by decide) (by decide) (by decide)
      demoTieNorm demoTieMin demoTieFirst (by simp) (hmod _)
    -- the SCALE BOUNDARY response: confidence AT 100 (constructed, the
    -- readout never reaches it) for the τ = 100 gate case
    let actRespBnd := actOfDists ["deploy", "rollback", "wait"] demoDists "deploy"
      100 2 (by decide) (by decide) (by decide)
      demoNorm demoSel_min3 demoSel_first3 (by simp) (by decide)
    -- List String toString drops the quotes; re-add them for valid JSON
    let gatesQ := toString (gates.map (fun s => "\"" ++ s ++ "\""))
    let labelsQ := toString (["alpha", "beta", "gamma"].map (fun s => "\"" ++ s ++ "\""))
    let j := "{\"conf_trace\": " ++ toString trace
      ++ ", \"reinjected_raw_trace\": " ++ toString reinj
      ++ ", \"is_hard_K2\": " ++ toString hard
      ++ ", \"gate_tau\": " ++ gatesQ
      ++ ", \"probs_trace\": " ++ toString probs
      ++ ", \"gate_calib_cases\": " ++ gcCases
      ++ ", \"loop_response_wrong_loop\": \"" ++ lrCase ++ "\""
      ++ ", \"multi_labels\": " ++ labelsQ
      ++ ", \"multi_conf_trace\": " ++ mConfs
      ++ ", \"multi_probs_trace\": " ++ mProbs
      ++ ", \"multi_gate_tau\": " ++ mGates
      ++ ", \"multi_gate_tau_updated\": " ++ mGatesU
      ++ ", \"multi_labels_updated\": " ++ mLabelsU
      -- the SCORE contract (v1.5.1): value/conf from DIFFERENT loops, each
      -- response carries confidenceLoopIdx; the calibration carries loopIdx
      -- and applies only at ITS loop; gateScore payload = the VALUE
      ++ ", \"score_value\": " ++ toString (rd 2 (iter F 2 H0))
      ++ ", \"score_conf\": " ++ toString (rd 5 (iter F 5 H0))
      ++ ", \"score_conf_loop\": 5"
      ++ ", \"score_gate\": \"" ++ (match gateScore ⟨tau0, hcert0, 5⟩
            { value := rd 2 (iter F 2 H0), confidence := rd 5 (iter F 5 H0),
              confidenceLoopIdx := 5,
              value_le_100 := hmod _, conf_le_100 := hmod _ } with
           | some _ => "argmax" | none => "none") ++ "\""
      -- POSITIVE path: loop MATCHES (2), conf 84 >= tau0 -> some value(52);
      -- the payload is the value, NOT the confidence (84)
      ++ ", \"score_payload_positive\": " ++ (match gateScore ⟨tau0, hcert0, 2⟩
            { value := rd 6 (iter F 6 H0), confidence := rd 2 (iter F 2 H0),
              confidenceLoopIdx := 2,
              value_le_100 := hmod _, conf_le_100 := hmod _ } with
           | some v => toString v | none => "null")
      ++ ", \"score_gate_positive\": \"" ++ (match gateScore ⟨tau0, hcert0, 2⟩
            { value := rd 6 (iter F 6 H0), confidence := rd 2 (iter F 2 H0),
              confidenceLoopIdx := 2,
              value_le_100 := hmod _, conf_le_100 := hmod _ } with
           | some _ => "argmax" | none => "none") ++ "\""
      -- WRONG loop: calib bound to loop 5, confidence from loop 2 -> none
      -- even though 84 >= tau0 (isolates the loop check)
      ++ ", \"score_gate_wrong_loop\": \"" ++ (match gateScore ⟨tau0, hcert0, 5⟩
            { value := rd 6 (iter F 6 H0), confidence := rd 2 (iter F 2 H0),
              confidenceLoopIdx := 2,
              value_le_100 := hmod _, conf_le_100 := hmod _ } with
           | some _ => "argmax" | none => "none") ++ "\""
      -- the SCALE BOUNDARY: τ = 100 (largest representable threshold)
      -- with a confidence AT the boundary (100) — the gate decides; the
      -- trace readouts never reach 100, so this is constructed directly
      ++ ", \"score_gate_boundary\": \"" ++ (match gateScore ⟨100, by decide, 2⟩
            { value := rd 6 (iter F 6 H0), confidence := 100,
              confidenceLoopIdx := 2,
              value_le_100 := hmod _, conf_le_100 := by decide } with
           | some _ => "argmax" | none => "none") ++ "\""
      ++ ", \"score_gate_updated\": " ++ (match gateScore ⟨tau0, hcert0, 5⟩
            (scoreOfDist [(30, 40), (70, 60)] (rd 5 (iter F 5 H0)) 5
              demoDist_vals demoDist_sum (hmod _)) with
           | some v => toString v | none => "null")
      ++ ", \"score_ev\": " ++ toString (expectedValue [(30, 40), (70, 60)])
      ++ ", \"score_exact_num\": " ++ toString (exactEVnum [(30, 40), (70, 60)])
      -- the ACT contract (v1.6.2): 3 actions with different cost
      -- distributions (each entry a CostEntry with its own scale proof;
      -- weights normalized to 100), selection by MINIMUM exact cost with
      -- the FIRST-DECLARED tie-break (sel_first) — the responses are
      -- CONSTRUCTED via actOfDists and every gate result is COMPUTED by
      -- gateAct, never a literal
      ++ ", \"act_actions\": " ++ toString (["deploy", "rollback", "wait"].map (fun s => "\"" ++ s ++ "\""))
      ++ ", \"act_cost_nums\": " ++ toString actResp.exactCostNums
      ++ ", \"act_selected\": \"" ++ actResp.selected ++ "\""
      ++ ", \"act_conf\": " ++ toString actResp.confidence
      ++ ", \"act_conf_loop\": " ++ toString actResp.confidenceLoopIdx
      ++ ", \"act_gate\": \"" ++ (match gateAct ⟨tau0, hcert0, 5⟩ actResp with
           | some _ => "decided" | none => "none") ++ "\""
      ++ ", \"act_gate_payload\": " ++ (match gateAct ⟨tau0, hcert0, 5⟩ actResp with
           | some a => "\"" ++ a ++ "\"" | none => "null")
      -- POSITIVE path: calib bound to loop 2, confidence from loop 2
      -- (conf 84 ≥ τ): payload = the ACTION, COMPUTED by gateAct
      ++ ", \"act_gate_positive\": \"" ++ (match gateAct ⟨tau0, hcert0, 2⟩ actRespPos with
           | some _ => "decided" | none => "none") ++ "\""
      ++ ", \"act_gate_payload_positive\": " ++ (match gateAct ⟨tau0, hcert0, 2⟩ actRespPos with
           | some a => "\"" ++ a ++ "\"" | none => "null")
      -- the SCALE BOUNDARY: τ = 100 with the constructed confidence AT
      -- 100 — the act gate decides and the payload is the action
      ++ ", \"act_gate_boundary\": \"" ++ (match gateAct ⟨100, by decide, 2⟩ actRespBnd with
           | some _ => "decided" | none => "none") ++ "\""
      ++ ", \"act_gate_payload_boundary\": " ++ (match gateAct ⟨100, by decide, 2⟩ actRespBnd with
           | some a => "\"" ++ a ++ "\"" | none => "null")
      -- the TIE-BREAK case: two actions with EQUAL exact numerators —
      -- the FIRST-declared one is selected (rollback before wait), the
      -- selection PROVED via demoTieMin/demoTieFirst and exported from the
      -- constructed response; gateAct COMPUTED
      ++ ", \"act_tie_actions\": " ++ toString (["rollback", "wait"].map (fun s => "\"" ++ s ++ "\""))
      ++ ", \"act_tie_cost_nums\": " ++ toString actRespTie.exactCostNums
      ++ ", \"act_tie_selected\": \"" ++ actRespTie.selected ++ "\""
      ++ ", \"act_tie_gate_positive\": \"" ++ (match gateAct ⟨tau0, hcert0, 2⟩ actRespTie with
           | some _ => "decided" | none => "none") ++ "\""
      ++ ", \"act_tie_gate_payload_positive\": " ++ (match gateAct ⟨tau0, hcert0, 2⟩ actRespTie with
           | some a => "\"" ++ a ++ "\"" | none => "null")
      ++ "}"
    IO.println j
    return 0
  | _ => do
    IO.eprintln "usage: ExportVectors A B M W R H0 TAU"
    return 1
