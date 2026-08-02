/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GRDefs

/-!
# B2D/GR4_gradedRead — the (i-b) seam theorem  [B2DEF_LEAN unit GR-4; wave 2a]

Blueprint §4 (the discharger target, RESTRUCTURED per R1-C1/C2/C3/C4) + §5 GR-4.
moves_ref: §B2-DEF D.5; H1_BM2 §S4 (i-b); B-M1 §S1.3/§S3.2. deps: GR-3.
difficulty: medium. REUSE: `GenuineStageModel.discharge`, `L4_grRes_eq_genuine`.

E-phase file: statement only, sorry body = the open-goals ledger.

## The consumption chain, DISPLAYED (nothing rebuilt) [R1-C5 fold]

(i-b) discharged on the [NR] carriers = `graded_read` (below) + B-M1 §S3.2's
VERIFIED arithmetic ((SL-dev)+(SL-top) ⟹ (K0)+(K1)+(K2) with U₀ = 1). A KP-STEP
application additionally consumes `kp_step` AS LANDED
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
the (i-b) identity at the parent read. -/
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

end LeanUrat.B2D
