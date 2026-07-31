import Mathlib
import LeanUrat.HC2.HK23_twoNodeGatePos

/-!
# HK-52 STRETCH GATE — the compiled child-pair stretch mechanism at the (NEW) keying
(post-wave unit, 2026-07-31; BP2 sequencing HK-12 → HK-52; agent: post-wave-1)

## What this leaf is

The HK-06 wave (QUEUE_EXECUTION_2026-07-31.md §Item 3) reopened the four V9 sorries
(`HC1/V9_K1nonrec.lean`: `V9_K1nonrec`/`V9_E1box_nonrec`, steep + corner legs) as the
HK-52/HK-11a/HK-11b obligation, flagging the displayed ℚ-form
`σ_{i+1}.w (B μ) = strFrame(i+1) · lineᵢ.at(μ·childWidthᵢ)` as possibly needing "the
ν_{i+1}.e-stretch factor".  This leaf COMPILES that mechanism, per the HK-12 re-check
(`verification/hk12_recheck.py`, five asserted findings F1–F5, all green 2026-07-31):

* `hk52_qform_stretch` — at ANY recorded transition record (the (S-a) STEP-2
  `TransitionCoreL σV σ'` at the child pair), the child weight of every child-key
  coefficient carries the CHILD node's stride: `σ'.w B = e′ · σV.w B`.  Pure Stage-law
  arithmetic (`hStretch` + `child_e` + `child_wPrev`) — no ReadsOf, no side data.
* `hk52_history_child_stretch` — the same read off a coherent history's
  non-recentering step (the recorded σV surfaced from the (NEW) leg).
* `hk52_v9_qform_reduction` — THE REDUCTION: V9's displayed ℚ-form at step (i, i+1)
  is EQUIVALENT to `(ν_{i+1}.e : ℚ) · σV.w (B μ) = strFrame(i+1) · lineᵢ.at(μ·cwᵢ)`.
  Since `strFrame(i+1)` contains NO ν_{i+1}.e factor (it is the product of the
  PARENT-side read strides — all 1 on the RG-2 recorded perimeter), the ν_{i+1}.e
  stretch sits on the LEFT of the reduced form only: the displayed form is TRUE on the
  `ν_{i+1}.e = 1` sub-perimeter (where the reduced form is the σV-vertex law
  = V4-(VERTEX) content at the recorded regrade) and FALSE-SUSPECT at every
  `ν_{i+1}.e ≥ 2` record with nonzero vertex value.
* `hk52_gate_stretch_two` — the compiled COHERENT-REACHABLE factor-2 instance: at
  HK23's positive gate (H₂ram: bStageP → ramifiedStage, child pair (2,5), the wave's
  own de-vacuity carrier) the stretch factor is literally 2 on every child-key
  coefficient.

## The re-adjudication record (HK-12 findings, compiled/numeric split)

F1 The r3b countermodel data are NOT excluded at the `RegradeOf` layer (σV.w is
   slot-min-FORCED; the D.7(i)–(v) residual laws were never ratified).  [numeric]
F2 THE CURE: at child pair e′ = 1 the r3b data now SATISFY the kernel conclusion —
   `σ'.wPrev = σV.w` lands on the regrade (= wV), so `σ'.w(B₂) = 1·wV(B₂) = 2 =`
   target.  R3b's bottom-window law DISSOLVES for V9's steep legs.  [numeric; the
   compiled half is `hk52_qform_stretch`]
F3 BP2 HK-11a's DISPLAYED law (`σ'.wPrev (B μ) = νᵢ.e·σᵢ.w (B μ)`) stays REFUTED on
   the r3b data even under (NEW) (2 ≠ 1) — and V9 never consumes it.  HK-11a must be
   RE-POINTED at the σV-vertex law `σV.w (B μ) = gam − μ·e★·g·h★` (V4-(VERTEX) at the
   recorded regrade + the R3a anchor transport).  [numeric]
F4 THE NEW OBSTRUCTION (this leaf): the ν_{i+1}.e stretch.  All four reopened V9
   sorries are, AS DISPLAYED, false-suspect at `ν_{i+1}.e ≥ 2` records (recordable:
   node i+1's own leg never fires when terminal; coherent carrier compiled at HK23).
   Residual to a full refutation = ReadsOf inhabitation at ONE ramified-terminal-child
   record — a Block-G-gate-scale build (HK-18/19/57/20/22-shaped), NOT built here.
   Residual to a full proof at ν_{i+1}.e = 1 = the σV-vertex law (R3a + the F5-degenerate
   interior story).  EITHER WAY the ν_{i+1}.e ≥ 2 disposition is an ADJUDICATION item
   (the Q2-extension ruling covered the PARENT read stride only): surface to the
   orchestrator — candidate dispositions mirror E-a (named hypothesis `σ_{i+1}.e = 1`
   on the legs, statement-fence event) vs a recording fence extension (R-tie-style
   guard already exists for the s/t ties).  DO NOT fill the V9 sorries before that
   ruling.
F5 INTERIOR DEGENERATION: at i ≥ 1 with non-recentering predecessor the frame pair
   IS the read pair and the e★ = 1 regrade is weight-IDEMPOTENT (σV.w = σᵢ.w), so
   HK-52's "per-slot forced-window recursion at σV" is the identity at interior
   reads; genuinely h-steep reads live at i = 0 / post-recentering only.  [numeric;
   idempotency compilable on demand from `hK1` + `hStretch` — not needed by V9's
   reduction, so not built here]

Statements of V9 are BYTE-UNTOUCHED (this is a leaf; consumers: none).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesJ

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesD

namespace HK52

/-- **The child-pair stretch law** at any (S-a) STEP-2 transition record: the child
stage weighs every child-key coefficient at the CHILD pair's stride over the recorded
regrade — `σ'.w B = e′ · σV.w B`.  Stage-law arithmetic only (`hStretch` at σ′ +
`child_e` + `child_wPrev`); no run data enter. -/
theorem hk52_qform_stretch {p : ℕ} [Fact p.Prime] {F : Type*} [Field F] [Finite F]
    {σV σ' : Stage p F} {Φhat : Polynomial ℤ_[p]} {e' h' : ℕ} {zbar : Fˣ}
    (htcore : TransitionCoreL σV σ' Φhat e' h' zbar)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0) (hin : inC Φhat B) :
    σ'.w B = (e' : ℤ) * σV.w B := by
  have hin' : inC σ'.Φ B := by rw [htcore.base.child_key]; exact hin
  have h1 := σ'.hStretch B hB hin'
  rw [htcore.base.child_e, htcore.base.child_wPrev] at h1
  exact h1

/-- The stretch law read off a coherent history's non-recentering step: the (NEW) leg
supplies the regrade σV, and the child frame's weight on every child-key coefficient
is `ν_{i+1}.e · σV.w`. -/
theorem hk52_history_child_stretch {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (B : Polynomial ℤ_[p]) (hB : B ≠ 0)
    (hin : inC (H.nodes[i+1]'hi1).σ.Φ B) :
    ∃ σV : Stage p F,
      RegradeOf (H.nodes[i]'(by omega)).σ (H.nodes[i]'(by omega)).e
          (H.nodes[i]'(by omega)).h σV ∧
        (H.nodes[i+1]'hi1).σ.w B = (((H.nodes[i+1]'hi1).e : ℤ)) * σV.w B := by
  obtain ⟨-, -, -, htrans⟩ := hcoh
  obtain ⟨-, hnrecC, -, -, -, -, -⟩ := htrans i hi1
  obtain ⟨-, σV, hreg, -, htcore⟩ := hnrecC hsp
  exact ⟨σV, hreg, hk52_qform_stretch htcore B hB hin⟩

/-- **THE V9 ℚ-FORM REDUCTION** (the compiled half of HK-12 finding F4): at a coherent
history's non-recentering step and any child-key development `B` of any `f` with
nonzero vertex coefficient, V9's DISPLAYED conclusion
`σ_{i+1}.w (B μᵢ) = strFrame(i+1) · lineᵢ.at(μᵢ·childWidthᵢ)` is EQUIVALENT to the
ν_{i+1}.e-scaled σV-form.  `strFrame(i+1)` carries no `ν_{i+1}.e` factor, so the
displayed form is exactly the σV-vertex law WHEN `ν_{i+1}.e = 1`, and is off by the
factor `ν_{i+1}.e` otherwise. -/
theorem hk52_v9_qform_reduction {p : ℕ} [Fact p.Prime] {F : Type*} [Field F]
    [Finite F] {H : History p F} (hcoh : HistoryCoherent H)
    (i : ℕ) (hi1 : i + 1 < H.nodes.length)
    (hsp : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (f : Polynomial ℤ_[p]) (B : ℕ → Polynomial ℤ_[p]) (Nd : ℕ)
    (hdev : IsDevelopment (H.nodes[i+1]'hi1).σ.Φ f B Nd)
    (hBμ : B (H.nodes[i]'(by omega)).μ ≠ 0) :
    ∃ σV : Stage p F,
      RegradeOf (H.nodes[i]'(by omega)).σ (H.nodes[i]'(by omega)).e
          (H.nodes[i]'(by omega)).h σV ∧
      ((((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
          = (H.strFrame (i+1) : ℚ) *
            (H.nodes[i]'(by omega)).line.at
              ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)
        ↔ (((H.nodes[i+1]'hi1).e : ℚ))
              * ((σV.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ))
            = (H.strFrame (i+1) : ℚ) *
              (H.nodes[i]'(by omega)).line.at
                ((H.nodes[i]'(by omega)).μ * (H.nodes[i]'(by omega)).childWidth)) := by
  obtain ⟨σV, hreg, hz⟩ := hk52_history_child_stretch hcoh i hi1 hsp
    (B ((H.nodes[i]'(by omega)).μ)) hBμ (hdev.1 _)
  refine ⟨σV, hreg, ?_⟩
  have hq : (((H.nodes[i+1]'hi1).σ.w (B ((H.nodes[i]'(by omega)).μ)) : ℤ) : ℚ)
      = (((H.nodes[i+1]'hi1).e : ℚ))
          * ((σV.w (B ((H.nodes[i]'(by omega)).μ)) : ℚ)) := by
    exact_mod_cast congrArg (fun z : ℤ => (z : ℚ)) hz
  rw [hq]

/-- **The compiled coherent-reachable stretch-2 instance** (HK-12 finding F4's
carrier): at the HK23 positive gate's recorded STEP-2 transition (bStageP root read →
`R7Forge.ramifiedStage` at the child pair (2, 5) — the wave's own `H₂ram`, proved
`HistoryCoherent ∧ Realizable ∧ InBox`), the child frame weighs every child-key
coefficient DOUBLE the recorded regrade: the ν₁.e-stretch is inhabited at a coherent
record, not a hypothetical. -/
theorem hk52_gate_stretch_two (B : Polynomial ℤ_[2]) (hB : B ≠ 0)
    (hin : inC U31.fq B) :
    R7Forge.ramifiedStage.w B = 2 * HK23.σVgate.w B := by
  have h := hk52_qform_stretch HK23.tcl_gate B hB hin
  exact_mod_cast h

end HK52

end LeanUrat.MovesJ

#print axioms LeanUrat.MovesJ.HK52.hk52_qform_stretch
#print axioms LeanUrat.MovesJ.HK52.hk52_history_child_stretch
#print axioms LeanUrat.MovesJ.HK52.hk52_v9_qform_reduction
#print axioms LeanUrat.MovesJ.HK52.hk52_gate_stretch_two
