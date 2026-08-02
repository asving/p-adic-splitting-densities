/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GRDefs

/-!
# B2D/GR2_slotResidual — the per-κ (SL-dev) display  [B2DEF_LEAN unit GR-2; wave 2a]

Blueprint §5 GR-2. moves_ref: §B2-DEF D.5 RESIDUAL (MOVES :2270–2277), D.3(c)
stride. deps: E1, GR-0 (residue displayed). difficulty: medium.
REUSE: `H1.stage_R_pow`, `L3_residual_mul`/S9w `hRmul`, the `nodeLift_key_res`
pattern.

E-phase file: statements only, sorry bodies = the open-goals ledger. Under the
(P4) dictionary the σ.R-face + Θ-image below IS B-M1's (SL-dev)
`in(D_κΦ^{eκ}) = U₀ψ_κϕ_{γ̂}ȳ^κ` (the T-monomial at the stride position;
blueprint §4's per-κ display note).

STATEMENT FLAG (N-GR1 gate): `GR2_posStep`'s unit-step display is the blueprint's
D.3(c) stride prediction; the §7 falsifier family N-GR1 (per-κ harness at e′ ≥ 2,
g ≥ 2, σ.t ≠ 0) gates it and runs BEFORE proof effort — a refutation there
re-adjudicates the statement (scale/exponent defect class, the HK52 precedent),
never silently weakens it.
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesGr

universe u
variable {p : ℕ} [Fact p.Prime] {F : Type u} [Field F] [Finite F]

/-- **GR-2, σ.R-face of the per-κ (SL-dev)**: each present slot's residual is the
single ψ-digit monomial at the position functional `readPos` (positions forced by
the `IsNodeLift` (S5) field + the pinned key residual `hRΦ` through `hRmul`). -/
theorem GR2_slotResidual (ν : Node p F) (R : ReadHyps ν)
    (tt : ℕ → Polynomial ℤ_[p]) (κ : ℕ) (hκ : κ < ν.g) (hψκ : ν.ψ.coeff κ ≠ 0)
    (htt0 : tt κ ≠ 0)
    (httR : ν.σ.R (tt κ) = LaurentPolynomial.C (ν.ψ.coeff κ) *
      LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (tt κ))) :
    ν.σ.R (tt κ * ν.σ.Φ ^ (ν.e * κ)) =
      LaurentPolynomial.C (ν.ψ.coeff κ) * LaurentPolynomial.T (readPos ν tt κ) := by
  sorry -- B2DEF_LEAN E-phase sorry [unit GR-2]

/-- **GR-2 stride law (D.3(c) at the read)**: `readPos` is affine in κ with UNIT
κ-step across present slots — the exponent pin `ReadHyps.hbez`/`hscale` +
`Stage.hStretch` arithmetic. GATED by falsifier family N-GR1 (module docstring
flag) — the harness runs before any proof attempt. -/
theorem GR2_posStep (ν : Node p F) (R : ReadHyps ν)
    (tt : ℕ → Polynomial ℤ_[p]) (κ : ℕ)
    (htt0 : tt κ ≠ 0) (htt0' : tt (κ + 1) ≠ 0)
    (httC : inC ν.σ.Φ (tt κ)) (httC' : inC ν.σ.Φ (tt (κ + 1)))
    (httw : ν.σ.w (tt κ) = (ν.h : ℤ) * ((ν.g : ℤ) - (κ : ℤ)))
    (httw' : ν.σ.w (tt (κ + 1)) = (ν.h : ℤ) * ((ν.g : ℤ) - ((κ : ℤ) + 1))) :
    readPos ν tt (κ + 1) = readPos ν tt κ + 1 := by
  sorry -- B2DEF_LEAN E-phase sorry [unit GR-2]

/-- **GR-2 Θ-image corollary (the per-κ (i-b) display)**: the slot residual read
through the parent model's `discharge` — the graded face of (SL-dev), in the
`Stage.grRes` normal form `C(σ.R f)·T^{σ.w f}` (exact form fixed by the E-phase
probe against `GenuineStageModel.Θ`/`LExt`). -/
theorem GR2_slotResidual_graded (ν : Node p F) (Mpar : GenuineStageModel ν.σ)
    (R : ReadHyps ν)
    (tt : ℕ → Polynomial ℤ_[p]) (κ : ℕ) (hκ : κ < ν.g) (hψκ : ν.ψ.coeff κ ≠ 0)
    (htt0 : tt κ ≠ 0)
    (httR : ν.σ.R (tt κ) = LaurentPolynomial.C (ν.ψ.coeff κ) *
      LaurentPolynomial.T (- ν.σ.t * ν.σ.wPrev (tt κ))) :
    (letI := Mpar.Rg.ring; letI := Mpar.Loring; letI := Mpar.alg;
      Mpar.Θ (algebraMap Mpar.S.Gr Mpar.Lo
          (Mpar.S.initialForm (tt κ * ν.σ.Φ ^ (ν.e * κ))))
        = LaurentPolynomial.C (LaurentPolynomial.C (ν.ψ.coeff κ) *
            LaurentPolynomial.T (readPos ν tt κ)) *
          LaurentPolynomial.T (ν.σ.w (tt κ * ν.σ.Φ ^ (ν.e * κ)))) := by
  sorry -- B2DEF_LEAN E-phase sorry [unit GR-2]

end LeanUrat.B2D
