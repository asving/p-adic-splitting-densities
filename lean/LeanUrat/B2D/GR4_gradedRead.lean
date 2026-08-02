/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GRDefs
import LeanUrat.B2D.GR0b_suppliers
import LeanUrat.B2D.GR1_equalWeights
import LeanUrat.B2D.GR3_keyResidual

/-!
# B2D/GR4_gradedRead — the (i-b) seam theorem  [B2DEF_LEAN unit GR-4; wave 2a]

Blueprint §4 (the discharger target, RESTRUCTURED per R1-C1/C2/C3/C4) + §5 GR-4.
moves_ref: §B2-DEF D.5; H1_BM2 §S4 (i-b); B-M1 §S1.3/§S3.2. deps: GR-3.
difficulty: medium. REUSE: `GenuineStageModel.discharge`, `Stage.grRes`.

## WAVE-2a ADJUDICATION (2026-08-02)

The frozen `graded_read` inherits GR-3's frame-side residue THROUGH ITS CLAUSE 2
(the ∃-form is exactly `GR3_keyResidual`; the σ.e-compression countermodel — GR-3
module docstring + N-GR1 check N5 — kills clause 2, hence the conjunction, at the
abstract carrier; clause 1 (K1) alone survives, PROVED as `GR1_equalWeights`).
Per the frozen-interface discipline (§4 UNTOUCHABLE; "if the interface genuinely
will not admit the proof, STOP with the frozen goal") the E-phase sorry STANDS
byte-unchanged. The PROVED route (new supplier lemmas, sanctioned):

* `graded_read_level` — the frozen three-clause conclusion WITH the two frame pins
  `ν.σ.s = 1`, `ν.σ.t = 0` (GR-3's exact residue; nothing else changes).
* `graded_read_of_history` — **the consumer-ready (i-b) discharger**: at an
  interior read of a coherent history (non-root, frame-creating transition
  non-recentering, read level — the recorded [NR] perimeter, exactly where B-M2's
  (i-b) row lives), the pins and the whole `ReadHyps` pack are SUPPLIED by
  `GR0b`'s history suppliers, so the three-clause conclusion holds with NO
  displayed wiring hypotheses beyond coherence itself + the parent model `Mpar`.

## The consumption chain, DISPLAYED (nothing rebuilt) [R1-C5 fold]

(i-b) discharged on the [NR] carriers = `graded_read_of_history` (above) + B-M1
§S3.2's VERIFIED arithmetic ((SL-dev)+(SL-top) ⟹ (K0)+(K1)+(K2) with U₀ = 1). A
KP-STEP application additionally consumes `kp_step` AS LANDED
(`Scaffold/HDischarge/H1/TowerStep.lean` — child model M, `DevBound` row,
untouched; their conditionality displayed there). The former corollary "GR-4b
`kpblock_of_read`" is DELETED by design review R1-C5 (it re-assembled `kp_step`'s
own fields) and is NOT an acceptance target [R2-C2]; fence (viii) prohibits any
`KPBlock` assembly here.

## Scope (per B-M2's own display)

This discharges (i-b): lift-level (K1)+(K2) on the [NR] carriers, GIVEN the
parent model `Mpar` (M-parametric — fence (i): no `GenuineStageModel` instance is
built). It does NOT touch SITE-EXH, REC-SL, TR-3-ORD-X, or A-M2 (§6 fences
(i)–(iii)).

## Third-clause probe record (the §4 "exact form: E-phase probe")

Through `Mpar.discharge`, `Θ(ι in(Φ′)) = σ.grRes Φ′ = C(σ.R Φ′)·T^{σ.w Φ′}`
(`Stage.grRes`, DefsL) — substituting clause 2 gives the compiled form below:
`C(T^{m̂}·toLaurent ψ)·T^{w Φ′}` in `LExt ↥σ.K = LTwo ↥σ.K` (outer `T` = the
grading variable, inner ring = the residual Laurent ring). This is the (P4)
rendering of B-M1's `R^gr_{γ̂}(in Φ_{i+1}) = U₀·ψ` with U₀ = 1.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesGr

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **GR-4 `graded_read` — the (i-b) seam theorem** (blueprint §4, the three-clause
conclusion): at any fired lift `Φ′` of the node ν (the `IsNodeLift` hard-wired
stage-law data), given the parent model and the displayed wiring pack,
(K1) the parent weight, (K2) the Laurent face (fills `GrBKeyLaws.key_res` with
c = 1, k = m̂), and (K2)'s GRADED face through the parent model's Θ/discharge —
the (i-b) identity at the parent read. **WAVE-2a STATUS: OPEN-OBSTRUCTED at the
frozen signature** (clause 2 = GR-3's ∃-form, whose frame-side residue is genuine —
module docstring); the PROVED forms are `graded_read_level` /
`graded_read_of_history` below. -/
theorem graded_read (ν : Node p F) (Mpar : GenuineStageModel ν.σ)
    (Φ' : Polynomial ℤ_[p]) (hlift : IsNodeLift ν Φ') (R : ReadHyps ν) :
    -- (K1), parent weight:
    (ν.σ.w Φ' = (ν.e : ℤ) * (ν.g : ℤ) * ν.σ.w ν.σ.Φ)
    -- (K2), Laurent face:
    ∧ (∃ mh : ℤ, ν.σ.R Φ' = LaurentPolynomial.T mh * Polynomial.toLaurent ν.ψ)
    -- (K2), GRADED face — the (i-b) identity through the parent model
    -- (via Mpar.discharge: Θ(ι in(Φ')) = σ.grRes Φ' = C(σ.R Φ')·T^{w Φ'}):
    ∧ (letI := Mpar.Rg.ring; letI := Mpar.Loring; letI := Mpar.alg;
        ∃ mh : ℤ,
          Mpar.Θ (algebraMap Mpar.S.Gr Mpar.Lo (Mpar.S.initialForm Φ'))
            = LaurentPolynomial.C (LaurentPolynomial.T mh * Polynomial.toLaurent ν.ψ)
              * LaurentPolynomial.T (ν.σ.w Φ')) := by
  sorry -- B2DEF_LEAN E-phase sorry [unit GR-4]

/-- **GR-4, SUPPLIER-LEVEL, PROVED**: the frozen three-clause conclusion under the
two frame pins (GR-3's exact residue). Clause 1 = `GR1_equalWeights` (general, no
pins); clause 2 = `GR3_keyResidual_level` at `mh = ν.mhat = 0`; clause 3 = clause 2
pushed through `Mpar.discharge` + `Stage.grRes`. -/
theorem graded_read_level (ν : Node p F) (Mpar : GenuineStageModel ν.σ)
    (Φ' : Polynomial ℤ_[p]) (hlift : IsNodeLift ν Φ') (R : ReadHyps ν)
    (hσs : ν.σ.s = 1) (hσt : ν.σ.t = 0) :
    (ν.σ.w Φ' = (ν.e : ℤ) * (ν.g : ℤ) * ν.σ.w ν.σ.Φ)
    ∧ (∃ mh : ℤ, ν.σ.R Φ' = LaurentPolynomial.T mh * Polynomial.toLaurent ν.ψ)
    ∧ (letI := Mpar.Rg.ring; letI := Mpar.Loring; letI := Mpar.alg;
        ∃ mh : ℤ,
          Mpar.Θ (algebraMap Mpar.S.Gr Mpar.Lo (Mpar.S.initialForm Φ'))
            = LaurentPolynomial.C (LaurentPolynomial.T mh * Polynomial.toLaurent ν.ψ)
              * LaurentPolynomial.T (ν.σ.w Φ')) := by
  have h2 := GR3_keyResidual_level ν Φ' hlift R hσs hσt
  refine ⟨GR1_equalWeights ν Φ' hlift R, ⟨ν.mhat, h2⟩, ⟨ν.mhat, ?_⟩⟩
  rw [Mpar.discharge Φ' (nodeLift_ne_zero ν Φ' hlift), Stage.grRes, h2]

/-- **GR-4, THE HISTORY-LEVEL (i-b) DISCHARGER, PROVED** (the consumer-ready form):
at an interior read of a coherent history — non-root (`ν = H.nodes[i+1]`), frame
created by a non-recentering transition, read level (`ν.e = 1`; supplied on the
recorded perimeter by RG-2 at interior non-recentering reads and by `hspecRec` at
recenterings — `GR0b`) — the three-clause (i-b) conclusion holds given ONLY the
parent model. All wiring (the full `ReadHyps` pack incl. `hscale`/`hψ0` AND the
frame pins) is SUPPLIED by `HistoryCoherent` (`GR0b.readHyps_of_history` +
`GR0b.frame_level_of_history`): the displayed residues of the E-gate are fully
discharged on this carrier. -/
theorem graded_read_of_history {H : History p F} (hcoh : HistoryCoherent H)
    {i : ℕ} (hi : i + 1 < H.nodes.length)
    (hprev : (H.nodes[i]'(by omega)).species ≠ ReadSpecies.recentering)
    (he1 : (H.nodes[i+1]'hi).e = 1)
    (Mpar : GenuineStageModel (H.nodes[i+1]'hi).σ)
    (Φ' : Polynomial ℤ_[p]) (hlift : IsNodeLift (H.nodes[i+1]'hi) Φ') :
    ((H.nodes[i+1]'hi).σ.w Φ'
        = ((H.nodes[i+1]'hi).e : ℤ) * ((H.nodes[i+1]'hi).g : ℤ)
          * (H.nodes[i+1]'hi).σ.w (H.nodes[i+1]'hi).σ.Φ)
    ∧ (∃ mh : ℤ, (H.nodes[i+1]'hi).σ.R Φ'
        = LaurentPolynomial.T mh * Polynomial.toLaurent (H.nodes[i+1]'hi).ψ)
    ∧ (letI := Mpar.Rg.ring; letI := Mpar.Loring; letI := Mpar.alg;
        ∃ mh : ℤ,
          Mpar.Θ (algebraMap Mpar.S.Gr Mpar.Lo (Mpar.S.initialForm Φ'))
            = LaurentPolynomial.C (LaurentPolynomial.T mh
                * Polynomial.toLaurent (H.nodes[i+1]'hi).ψ)
              * LaurentPolynomial.T ((H.nodes[i+1]'hi).σ.w Φ')) := by
  have R := readHyps_of_history hcoh hi hprev he1
  have hlv := frame_level_of_history hcoh hi hprev he1
  exact graded_read_level _ Mpar Φ' hlift R hlv.1 hlv.2

end LeanUrat.B2D

#print axioms LeanUrat.B2D.graded_read_level
#print axioms LeanUrat.B2D.graded_read_of_history
