/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface

/-!
# LeanUrat.L6M4 — assembly: the per-type density is a uniform rational function of `q`

This is the **real derivation** (NOT an axiom) that the per-type factorization density `ρ(n,σ;q)`
is represented by a single rational function `num/den ∈ ℚ(t)` at every prime power `q`.

It derives this from two genuinely different inputs, neither of which is the conclusion:
* `DensityFoundation.decomposition` — the *structural* fact (L1 Hensel-splitting + cluster-tree
  stratification) that `ρ` is the finite multiplicity-weighted sum of per-**shape** cluster volumes
  `∑_{T ∈ shapes n σ} m_T(q) · C_T(q)`, with `m_T` a polynomial;
* `Interface.clusterVolume_rational` — the per-**shape** boundary (G-A′ / BB3-∞ ← GMN): each
  `C_T(q)` is a uniform rational function of `q`.

The mathematical content here is exactly "a finite sum of polynomial-multiplied rational functions
is a rational function" — proved by induction on the (finite) set of shapes, combining each term
over a common denominator. This is what makes the Goal Theorem MEAN the proof rather than assume it.

Citation: `notes/HUMAN_PROOF.md §10` (L6M4 assembly / linear system).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.L6M4

open Polynomial

/-- **Finite sum of rational functions is rational (with pole control at prime powers).**
For any finite set `S` of cluster shapes, the partial sum `∑_{T ∈ S} m_T(q)·C_T(q)` is represented
by a single `num/den ∈ ℚ(t)` with `den` nonvanishing at every `q > 1`. Proved by induction on `S`,
combining each new term over a common denominator. -/
theorem sum_clusterVol_rational (F : DensityFoundation) (Br : OMBridge F)
    (S : Finset ClusterShape) :
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧ ∀ q : ℕ, 1 < q →
      den.eval (q : ℚ) ≠ 0 ∧
      (∑ T ∈ S, (F.multiplicity T).eval (q : ℚ) * F.clusterVolume T q)
        = num.eval (q : ℚ) / den.eval (q : ℚ) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    refine ⟨0, 1, one_ne_zero, fun q hq => ⟨by simp, by simp⟩⟩
  | @insert T S hTS ih =>
    obtain ⟨A, B, hB, hAB⟩ := ih
    obtain ⟨nT, dT, hdT, hcT⟩ := clusterVolume_rational F Br T
    refine ⟨F.multiplicity T * nT * B + A * dT, dT * B, mul_ne_zero hdT hB, ?_⟩
    intro q hq
    obtain ⟨hBq, hABq⟩ := hAB q hq
    obtain ⟨hdTq, hcTq⟩ := hcT q hq
    refine ⟨?_, ?_⟩
    · simp only [Polynomial.eval_mul]
      exact mul_ne_zero hdTq hBq
    · rw [Finset.sum_insert hTS, hABq, hcTq]
      simp only [Polynomial.eval_add, Polynomial.eval_mul]
      field_simp

/-- **L6M4 — the per-type density is a uniform rational function of `q`.**
DERIVED from `DensityFoundation.decomposition` (structure) and `clusterVolume_rational` (per-shape
boundary) via `sum_clusterVol_rational`. This is the lemma the Goal Theorem consumes for its
rationality half; it is a genuine proof, not the conclusion-axiom of the earlier (vacuous) design. -/
theorem density_rational (F : DensityFoundation) (Br : OMBridge F) (n : ℕ) (σ : FactorizationType)
    (hσ : σ.degree = n) :
    ∃ num den : Polynomial ℚ, den ≠ 0 ∧ ∀ q : ℕ, 1 < q →
      den.eval (q : ℚ) ≠ 0 ∧ F.density n σ q = num.eval (q : ℚ) / den.eval (q : ℚ) := by
  obtain ⟨num, den, hden, hsum⟩ := sum_clusterVol_rational F Br (F.shapes n σ)
  refine ⟨num, den, hden, fun q hq => ?_⟩
  obtain ⟨hdenq, heq⟩ := hsum q hq
  refine ⟨hdenq, ?_⟩
  rw [F.decomposition n σ hσ q hq, heq]

end LeanUrat.L6M4
