/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132rp1

/-!
# Uniformity.ChapC.C132rp2 — the total μ₃ graded operator `s2Mu3GradedRes` (μ₃ campaign, node M3-RP2)

**[M3-RP2, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6, row M3-RP2): a
mechanical port of the μ₂ polynomial assembly (`C130rp1.lean:279-345`, Parts 3-4) to the
just-landed μ₃ recursive coefficient `s2Mu3Coeff` (C132rp1).  This node ASSEMBLES the total
operator `R_β(g) = Σ_t s2Mu3Coeff β g t · y^t` and lifts every coefficient-level pin C132rp1
already proved to the polynomial: the master coefficient law, range independence, finite
support (both the packaged `natDegree` bound and the raw `natDegree`-past form), and the
zero law at above-grade inputs (published Lemma 3.14's engine).  No new mathematics: every
theorem below is `C130rp1`'s Part 3/4 shape with `s2GradedCoeff`/`S2AboveGrade` replaced by
`s2Mu3Coeff`/`S2Mu3AboveGrade` and the μ₂ numeral `5` by the μ₃ numeral `21` (already baked
into `s2Mu3Coeff`'s own grade-bound pins, so no numeral appears here at all).

## What lands

* `s2Mu3GradedRes β g : Polynomial ((s2DepthTwo h2 hq).fld 2)`, the total μ₃ graded residual
  (published Def 3.13's `R_β(g) ∈ F[y]` at the μ₃ numerals) — `Σ t ∈ range (β+1), C
  (s2Mu3Coeff β g t) * X^t`, the SAME assembly shape as `s2GradedRes` (C130rp1).
* the shape pin: the operator has exactly the abstract `FGMNSourceData.gradedResidual` field
  shape `ℕ → Polynomial O → Polynomial (W.fld r)`, at the μ₃ occurrence.
* **the master coefficient law** `s2Mu3GradedRes_coeff`: `(s2Mu3GradedRes β g).coeff t =
  s2Mu3Coeff β g t` for EVERY `t` — the polynomial is determined by C132rp1's total
  coefficient function, off `Uniformity.Hensel.coeff_sum_range_C_mul_X_pow` and C132rp1's
  `s2Mu3Coeff_eq_zero_of_grade_lt`.
* **range independence** `s2Mu3GradedRes_eq_sum_range`: the assembling sum may be read over
  any range `M ≥ β + 1`, not just the canonical `β + 1`.
* **finite support**, packaged (`s2Mu3GradedRes_natDegree_le`: `natDegree (s2Mu3GradedRes β
  g) ≤ β`) and raw (`s2Mu3GradedRes_coeff_eq_zero_of_natDegree_lt`: coefficients whose
  abscissa passes `g.natDegree` vanish on the polynomial, lifting C132rp1's coefficient-level
  `s2Mu3Coeff_eq_zero_of_natDegree_lt`).
* **the zero law at above-grade inputs** `s2Mu3GradedRes_zero_of_above` (published Lemma
  3.14, the `graded_zero_of_above` field shape at the μ₃ occurrence): `S2Mu3AboveGrade β g →
  s2Mu3GradedRes β g = 0`.  UNLIKE the μ₂ Part 4 proof (which re-derives the gate negation
  from `S2AboveGrade_iff_dvSupp`/`dvSupp_le_of_slotOnGrade` inline, because no
  coefficient-level zero-above law existed yet at that node), this lifts DIRECTLY from
  C132rp1's already-landed coefficient-level `s2Mu3Coeff_eq_zero_of_above` — the campaign
  row's own division of labor ("the coefficient-level zero laws below are RP-2's inputs, not
  its outputs", C132rp1 Part 3 docstring) makes this proof a one-line rewrite, simpler than
  its μ₂ ancestor.
* the zero-polynomial tooth `s2Mu3GradedRes_zero`: the zero polynomial has zero graded
  residual at every grade (`0 ∈ P_β⁺` always, C132rp0's `S2Mu3AboveGrade_zero`).

## What this node does NOT claim (honesty scope)

No additivity/multiplicativity (published Cor 4.12: M3-RP3/RP5/RP6), no normalization
(published Def 3.15: M3-RP8), no `FGMNSourceData`/`FGMNSourceLaws` record (M3-FD0).  No law
in the μ₂ Part 3/4 bank failed to port (BLOCKED-BECAUSE: none — every law in
`C130rp1.lean:279-358` ported directly; the zero-above law even shortens, per above, because
its coefficient-level engine already exists at C132rp1 for the μ₃ occurrence).  The
OPEN-RP1-TRANSPORT faithfulness split stays exactly as C132rp1 left it (leg 2/3 open, leg 1
derived); no theorem here touches it.

**DEPENDS.** C132rp1 (`s2Mu3Coeff`, `s2Mu3Coeff_eq_zero_of_grade_lt`,
`s2Mu3Coeff_eq_zero_of_natDegree_lt`, `s2Mu3Coeff_eq_zero_of_above`) · C132rp0
(`S2Mu3AboveGrade`, `S2Mu3AboveGrade_zero`) · C130s2 (`s2DepthTwo`) · `Uniformity.Hensel`
(`coeff_sum_range_C_mul_X_pow`, transitively imported) · mathlib
(`Polynomial.natDegree_le_iff_coeff_eq_zero`, `Finset.sum_subset`).

## Status

Sorry-free, axiom-free (Lean core only); no new axiom, no `unsafe`, no statement invented
beyond the row's sketch and the μ₂ porting pattern.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132rp2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C35b Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C130s6 Uniformity.Density.Tower.C130rp0
open Uniformity.Density.Tower.C130rp1 Uniformity.Density.Tower.C130rp8
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Part 1 — ★ the TOTAL μ₃ graded operator `s2Mu3GradedRes`

The `C130fg` shape `ℕ → Polynomial O → Polynomial (W.fld r)` at the μ₃ occurrence, with `r`
read off the `s2Mu3Coeff` codomain `(s2DepthTwo h2 hq).fld 2` (C132rp1's `𝔽₃` reading). -/

/-- ★ **NODE RP-2 — the total μ₃ graded residual** `R_β(g) ∈ 𝔽₃[y]` (published Def 3.13 at
the μ₃ numerals): the polynomial whose `t`-th coefficient is C132rp1's gated recursive
coefficient `s2Mu3Coeff β g t`.  Junk-total outside exact grades; determined by its total
coefficient function via `s2Mu3GradedRes_coeff`. -/
noncomputable def s2Mu3GradedRes (β : ℕ) (g : Polynomial O) :
    Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  ∑ t ∈ Finset.range (β + 1), Polynomial.C (s2Mu3Coeff h2 hq β g t) * Polynomial.X ^ t

/-- shape pin: the operator has EXACTLY the abstract `FGMNSourceData.gradedResidual` field
shape at the μ₃ occurrence (C130fg, U9 Q2's polynomial-valued ruling). -/
noncomputable example : ℕ → Polynomial O → Polynomial ((s2DepthTwo h2 hq).fld 2) :=
  s2Mu3GradedRes h2 hq

/-- ★ **the master coefficient law** (proof-independence + finite-support pin): for EVERY
`t`, the `t`-th coefficient of `s2Mu3GradedRes β g` is `s2Mu3Coeff β g t` — the polynomial is
determined by the total coefficient function, so no assembly choice is visible. -/
theorem s2Mu3GradedRes_coeff (β : ℕ) (g : Polynomial O) (t : ℕ) :
    (s2Mu3GradedRes h2 hq β g).coeff t = s2Mu3Coeff h2 hq β g t := by
  unfold s2Mu3GradedRes
  rw [Uniformity.Hensel.coeff_sum_range_C_mul_X_pow]
  split_ifs with ht
  · rfl
  · exact (s2Mu3Coeff_eq_zero_of_grade_lt h2 hq (by omega)).symm

/-- **range independence** (proof-independence pin for the assembling sum): the sum may be
read over any range `M ≥ β + 1`. -/
theorem s2Mu3GradedRes_eq_sum_range (β : ℕ) (g : Polynomial O) {M : ℕ} (hM : β + 1 ≤ M) :
    s2Mu3GradedRes h2 hq β g
      = ∑ t ∈ Finset.range M, Polynomial.C (s2Mu3Coeff h2 hq β g t) * Polynomial.X ^ t := by
  unfold s2Mu3GradedRes
  refine Finset.sum_subset (fun x hx => ?_) fun t _ hts => ?_
  · rw [Finset.mem_range] at hx ⊢
    omega
  · rw [s2Mu3Coeff_eq_zero_of_grade_lt h2 hq
      (by rw [Finset.mem_range, not_lt] at hts; omega), Polynomial.C_0, zero_mul]

/-- **finite support, packaged**: `natDegree (s2Mu3GradedRes β g) ≤ β`. -/
theorem s2Mu3GradedRes_natDegree_le (β : ℕ) (g : Polynomial O) :
    (s2Mu3GradedRes h2 hq β g).natDegree ≤ β := by
  refine Polynomial.natDegree_le_iff_coeff_eq_zero.mpr fun N hN => ?_
  rw [s2Mu3GradedRes_coeff]
  exact s2Mu3Coeff_eq_zero_of_grade_lt h2 hq (by omega)

/-- **finite support, the natDegree form on the polynomial**: coefficients whose abscissa
passes the development length vanish — lifts C132rp1's coefficient-level
`s2Mu3Coeff_eq_zero_of_natDegree_lt`. -/
theorem s2Mu3GradedRes_coeff_eq_zero_of_natDegree_lt {β t : ℕ} (g : Polynomial O)
    (h : g.natDegree < β % 2 + 2 * t) :
    (s2Mu3GradedRes h2 hq β g).coeff t = 0 := by
  rw [s2Mu3GradedRes_coeff]
  exact s2Mu3Coeff_eq_zero_of_natDegree_lt h2 hq h

/-! ## Part 2 — the zero law at above-grade inputs (published Lemma 3.14; the FD-0 shape)

On `P_β⁺` — C132rp0's `S2Mu3AboveGrade`, `β < s2Hgt₃ g` — C132rp1 already proved every
coefficient vanishes (`s2Mu3Coeff_eq_zero_of_above`); this lifts that directly to the
polynomial. -/

/-- **the zero law at above-grade inputs** (published Lemma 3.14, the
`graded_zero_of_above` field shape at the μ₃ occurrence): `S2Mu3AboveGrade β g →
s2Mu3GradedRes β g = 0`. -/
theorem s2Mu3GradedRes_zero_of_above {β : ℕ} {g : Polynomial O}
    (h : S2Mu3AboveGrade h2 hq β g) : s2Mu3GradedRes h2 hq β g = 0 := by
  refine Polynomial.ext fun t => ?_
  rw [s2Mu3GradedRes_coeff, Polynomial.coeff_zero]
  exact s2Mu3Coeff_eq_zero_of_above h2 hq h t

/-- the zero polynomial has zero graded residual at every grade (`0 ∈ P_β⁺` always,
C132rp0's `S2Mu3AboveGrade_zero`). -/
theorem s2Mu3GradedRes_zero (β : ℕ) : s2Mu3GradedRes h2 hq β (0 : Polynomial O) = 0 :=
  s2Mu3GradedRes_zero_of_above h2 hq (S2Mu3AboveGrade_zero h2 hq β)

end S2

end Uniformity.Density.Tower.C132rp2

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132rp2.s2Mu3GradedRes
#print axioms Uniformity.Density.Tower.C132rp2.s2Mu3GradedRes_coeff
#print axioms Uniformity.Density.Tower.C132rp2.s2Mu3GradedRes_eq_sum_range
#print axioms Uniformity.Density.Tower.C132rp2.s2Mu3GradedRes_natDegree_le
#print axioms Uniformity.Density.Tower.C132rp2.s2Mu3GradedRes_coeff_eq_zero_of_natDegree_lt
#print axioms Uniformity.Density.Tower.C132rp2.s2Mu3GradedRes_zero_of_above
#print axioms Uniformity.Density.Tower.C132rp2.s2Mu3GradedRes_zero

end AxCheck
