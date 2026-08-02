/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.B2D.GRDefs
import LeanUrat.B2D.GR0b_suppliers
import LeanUrat.Scaffold.HDischarge.H1.Order1

/-!
# B2D/GR2_slotResidual — the per-κ (SL-dev) display  [B2DEF_LEAN unit GR-2; wave 2a]

Blueprint §5 GR-2. moves_ref: §B2-DEF D.5 RESIDUAL (MOVES :2270–2277), D.3(c)
stride. deps: E1, GR-0. difficulty: medium.
REUSE: `H1.stage_R_pow`, `Stage.hRmul`/`hRΦ`, `Stage.hStretch`,
`GR0b.readHyps_e_eq_one`/`readHyps_h_eq`.

**PROVED (wave 2a, 2026-08-02), at the frozen statements.** Under the (P4)
dictionary the σ.R-face + Θ-image below IS B-M1's (SL-dev)
`in(D_κΦ^{eκ}) = U₀ψ_κϕ_{γ̂}ȳ^κ` (the T-monomial at the stride position;
blueprint §4's per-κ display note).

STATEMENT FLAG (N-GR1 gate) — **GATE RUN 2026-08-02, GREEN, BEFORE these proofs**
(`verification/openmath/ngr1_slotpos_trace.py`; blueprint §7 run record): the
stride prediction (positions integral, affine, UNIT κ-step, `m̂ = −t·h·g` at the
canonical pair) verified exactly at every probed read, including the joint
`e′ = 2 ∧ g = 2 ∧ t ≠ 0` case the spec demanded (instance B, `x⁴ + 3x² + 18`).
`GR2_posStep`'s proof route is the harness's arithmetic: the frame stretch
(`Stage.hStretch`) gives `σ.e·step = ν.e` over ℤ, and `ReadHyps` forces `ν.e = 1`
(`readHyps_e_eq_one`), so `σ.e = step = 1` by integrality — the unit step needs NO
frame-side pin (contrast GR-3, where the ABSOLUTE positions, not just the step, are
consumed and the frame pins are a genuine residue). -/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.B2D

open Polynomial LeanUrat.Moves LeanUrat.MovesC LeanUrat.MovesGr
open LeanUrat.Scaffold.HDischarge.H1

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
  rw [ν.σ.hRmul _ _ htt0 (pow_ne_zero _ ν.σ.hmonic.ne_zero),
    stage_R_pow ν.σ ν.σ.Φ ν.σ.hmonic.ne_zero, ν.σ.hRΦ, httR,
    LaurentPolynomial.T_pow, mul_assoc, ← LaurentPolynomial.T_add, readPos]

/-- **GR-2 stride law (D.3(c) at the read)**: `readPos` is affine in κ with UNIT
κ-step across present slots. GATED by falsifier family N-GR1 — RUN 2026-08-02,
GREEN (module docstring). Proof: the frame stretch (`hStretch`) turns the recorded
weight drop `ν.h` into `σ.e·(wPrev κ − wPrev (κ+1))`, so over ℤ
`σ.e·step = σ.t·ν.h + σ.e·ν.e·σ.s = ν.e·(σ.t·σ.h + σ.e·σ.s) = ν.e` (by `hscale` +
the FRAME's Bézout law), and `ReadHyps` forces `ν.e = 1` (`readHyps_e_eq_one`), so
`σ.e·step = 1` in ℤ with `σ.e ≥ 1` pins `step = 1`. -/
theorem GR2_posStep (ν : Node p F) (R : ReadHyps ν)
    (tt : ℕ → Polynomial ℤ_[p]) (κ : ℕ)
    (htt0 : tt κ ≠ 0) (htt0' : tt (κ + 1) ≠ 0)
    (httC : inC ν.σ.Φ (tt κ)) (httC' : inC ν.σ.Φ (tt (κ + 1)))
    (httw : ν.σ.w (tt κ) = (ν.h : ℤ) * ((ν.g : ℤ) - (κ : ℤ)))
    (httw' : ν.σ.w (tt (κ + 1)) = (ν.h : ℤ) * ((ν.g : ℤ) - ((κ : ℤ) + 1))) :
    readPos ν tt (κ + 1) = readPos ν tt κ + 1 := by
  have he1 : ν.e = 1 := readHyps_e_eq_one ν R
  have hh : ν.h = ν.σ.h := readHyps_h_eq ν R
  -- the frame stretch on both realizers
  have hst : ν.σ.w (tt κ) = (ν.σ.e : ℤ) * ν.σ.wPrev (tt κ) :=
    ν.σ.hStretch _ htt0 httC
  have hst' : ν.σ.w (tt (κ + 1)) = (ν.σ.e : ℤ) * ν.σ.wPrev (tt (κ + 1)) :=
    ν.σ.hStretch _ htt0' httC'
  have hbez := ν.σ.hbez
  -- σ.e · step = ν.e = 1 over ℤ
  have key : (ν.σ.e : ℤ) * (readPos ν tt (κ + 1) - readPos ν tt κ) = 1 := by
    unfold readPos
    have hwκ : (ν.σ.e : ℤ) * ν.σ.wPrev (tt κ) = (ν.σ.h : ℤ) * ((ν.g : ℤ) - (κ : ℤ)) := by
      rw [← hst, httw, hh]
    have hwκ' : (ν.σ.e : ℤ) * ν.σ.wPrev (tt (κ + 1))
        = (ν.σ.h : ℤ) * ((ν.g : ℤ) - ((κ : ℤ) + 1)) := by
      rw [← hst', httw', hh]
    push_cast [he1]
    linear_combination ν.σ.t * hwκ - ν.σ.t * hwκ' + hbez
  have hEpos : (1 : ℤ) ≤ (ν.σ.e : ℤ) := by exact_mod_cast ν.σ.he
  rcases Int.mul_eq_one_iff_eq_one_or_neg_one.mp key with ⟨-, hstep⟩ | ⟨hE, -⟩
  · linarith
  · rw [hE] at hEpos; linarith

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
  have hne : tt κ * ν.σ.Φ ^ (ν.e * κ) ≠ 0 :=
    mul_ne_zero htt0 (pow_ne_zero _ ν.σ.hmonic.ne_zero)
  have hdis := Mpar.discharge _ hne
  rw [hdis, Stage.grRes, GR2_slotResidual ν R tt κ hκ hψκ htt0 httR]

end LeanUrat.B2D

#print axioms LeanUrat.B2D.GR2_slotResidual
#print axioms LeanUrat.B2D.GR2_posStep
#print axioms LeanUrat.B2D.GR2_slotResidual_graded
