/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib.Algebra.Polynomial.Degree.Lemmas
import Mathlib.Algebra.Polynomial.Eval.Degree

/-!
# Uniformity.ChapF.F03 — `resTwist` and its three conclusions (degree, monicity, roots)

**Chapter F, NODE F.03** [lemma] (`blueprint/CHAP-F_weld_layer.md` §4), ENV-F1 + `[Field K]`.
The monic-normalized residual twist by a unit `ξ` (`EFF.JD0.05` line 3, the perimeter
display's residual line: `R(y) ↦ ξ^{−deg R} · R(ξ·y)`, "the (ξ,w) overall unit dies in
monic form"). Stated as CONCLUSIONS per the WZ-BOX-7 rule (honesty F-3): degree, monicity,
root census — no clause says "the twist preserves types". The LAW that the weld's residuals
transform this way is F.04's carried perimeter (GRTJA arc 1/2, honesty F-7), never this
node's claim.

Were `axiom` stubs at stage 0e; PROVED here (unit OM-9, 2026-08-16; certified first by
`om9_weld_cert.py` LEG A3 — including the leading-coefficient invariance, which is
STRONGER than monicity preservation and is the actual proof route — with the wrong-sign
`ξ^{+deg}` mutant caught at F₄ and invisible at F₃, the involution separator).
-/

namespace Uniformity.Density.Weld

open Polynomial

/-- The monic-normalized residual twist by a unit `ξ` (`EFF.JD0.05` line 3). -/
noncomputable def resTwist {K : Type*} [Field K] (ξ : Kˣ) (R : K[X]) : K[X] :=
  C ((ξ : K) ^ R.natDegree)⁻¹ * R.comp (C (ξ : K) * X)

theorem natDegree_resTwist {K : Type*} [Field K] (ξ : Kˣ) (R : K[X]) :
    (resTwist ξ R).natDegree = R.natDegree := by
  rw [resTwist, natDegree_C_mul (inv_ne_zero (pow_ne_zero _ ξ.ne_zero)),
    natDegree_comp, natDegree_C_mul_X _ ξ.ne_zero, mul_one]

theorem monic_resTwist {K : Type*} [Field K] (ξ : Kˣ) {R : K[X]} (hR : R.Monic) :
    (resTwist ξ R).Monic := by
  have hq : (C (ξ : K) * X).natDegree ≠ 0 := by
    rw [natDegree_C_mul_X _ ξ.ne_zero]; exact one_ne_zero
  have : (resTwist ξ R).leadingCoeff = 1 := by
    rw [resTwist, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_comp hq,
      hR.leadingCoeff, one_mul, leadingCoeff_mul, leadingCoeff_C, leadingCoeff_X,
      mul_one, inv_mul_cancel₀ (pow_ne_zero _ ξ.ne_zero)]
  exact this

theorem isRoot_resTwist {K : Type*} [Field K] (ξ : Kˣ) (R : K[X]) (r : K) :
    (resTwist ξ R).IsRoot r ↔ R.IsRoot ((ξ : K) * r) := by
  simp only [resTwist, IsRoot, eval_mul, eval_C, eval_comp, eval_X]
  constructor
  · intro h
    rcases mul_eq_zero.mp h with h | h
    · exact absurd h (inv_ne_zero (pow_ne_zero _ ξ.ne_zero))
    · exact h
  · intro h
    rw [h, mul_zero]

end Uniformity.Density.Weld
