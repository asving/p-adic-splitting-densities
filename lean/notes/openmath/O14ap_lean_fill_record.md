# O-14a′ Lean fill record — R7-RUN (2026-07-31)

**Unit**: the `RunRealizerExists p (ZMod p)` fill per `O14ap_phaseB_attempt.md` §4.2
(the O-14a′ wave-2 math, PROVED: Thm 1 prime-field collapse + Thm 3 last-node flank +
Cor 4), consumed by `MovesD/R7_polFillReduction.canPolicyC_pin` to discharge TreeCan's
(†15) pair.  Statements byte-unchanged everywhere; new module + two sorry fills only.

## Deliverables

1. **`lean/LeanUrat/MovesD/R7_runRealizer.lean`** (new leaf, 0 sorry, Lean-core):
   * `subfield_zmod_eq_top`, `node_g_eq_one` — Thm 1(i);
   * `frame_deg_one` — Thm 1(ii) (width-chain induction; rides the RG-2 fence AS A
     HYPOTHESIS, exactly where the recipe says so);
   * `stage_w_key_sub_lift` — the Lemma-3.2(iii) no-jump law (`hRlt` + `hRΦ` +
     coefficient extraction at 0 via `ResVal.CT_apply`);
   * `slotmin_w_linear_lift` — Lemma 3.1(b) on the (e = g = 1)-collapsed `IsNodeLift`
     display; `strFrame_eq_one` + `node_h_lt_h_succ` — Lemma 3.1(c) ((C2) + (C7) at
     unit scales); `exists_run_start` — the terminal-run anchor (downward strong
     induction off `root_iff`);
   * `terminal_center_realizer` — **THEOREM 3 at ZMod p** (`hS6b` at the anchor stage;
     `Nat.le_induction` transport of w/h/digPrime along the `IsRecenteringCore.base`
     records; `hS5` read-back pins the digit to the recorded center);
   * `runRealizerExists_zmod` — **COROLLARY 4** (interior leg =
     `interior_center_realizer_exists` + support-free-at-linear-frames Thm 1(iii);
     terminal leg = Theorem 3).
2. **`MovesD/TreeCan.lean`**: `canPolicy p := canPolicyC p (ZMod p)`,
   `canPolicy_pin p := canPolicyC_pin (runRealizerExists_zmod p)` — the two (†15)
   sorries FILLED, signatures byte-unchanged, dated discharge + scope note added.

## Footprint delta (the charged report)

| decl | BEFORE | AFTER |
|---|---|---|
| `MovesD.canPolicy` | propext, **sorryAx**, Classical.choice, Quot.sound | propext, Classical.choice, Quot.sound |
| `MovesD.canPolicy_pin` | propext, **sorryAx**, Classical.choice, Quot.sound | propext, Classical.choice, Quot.sound |
| `MovesU.bridgePol` | propext, **sorryAx**, Classical.choice, Quot.sound | propext, Classical.choice, Quot.sound |
| `MovesU.bridgeTm` | propext, **sorryAx**, Classical.choice, Quot.sound | propext, Classical.choice, Quot.sound |
| `MovesU.bridgeClassifierSpec` | core-only (already) | unchanged |
| `MovesU.bridgeFibers` | core-only (already) | unchanged |
| `MovesU.bridgeTreePin` | core-only (already) | unchanged |

Note on the charge's naming: `bridgeClassifierSpec`/`bridgeFibers`/`bridgeTreePin`
were ALREADY Lean-core before the fill — they are policy-PARAMETRIC (bind
`OffsetPPin pol`, never the pinned pair); the D-group sorryAx they conditioned on
flowed through the WIRE `bridgePol`/`bridgeTm` (BridgeD1_treeModelWire), which is the
pair that improves.  The R7 designer chain's sorryAx source is DEAD.

Gates: full `lake build` green (8579 jobs); `lake env lean LeanUrat/AxChk_baseline.lean`
clean — 740 footprints, ZERO sorryAx, both density capstones
(`montes_unconditional_w`, `RealInstanceV2.montes_unconditional`) unchanged Lean-core.

## Honest scope (report with any citation of this discharge)

* **RG-2 fence**: `frame_deg_one` consumes the recording fence; a fence lift REOPENS
  the (CR2) support clause at ZMod p (O-14a′ §5.5) — the (S6b′-SUPP) re-adjudication
  is a PREREQUISITE of any fence lift.  Named forward obligation.
* **Thinness**: recorded towers over the prime ambient field are linear-key
  (order-0-slice-consistent, disclosed).
* **General F**: the compiled (CR2) is REFUTED-AS-STATED (O-14a′ Thm 5, (3, 𝔽₉));
  nothing here quantifies past F = ZMod p.

Records also in: `MovesD/MANIFEST.json` key `r7_run_fill_2026-07-31`;
`docs/PROJECT_STATE.md` recent-results item 6 addendum.
