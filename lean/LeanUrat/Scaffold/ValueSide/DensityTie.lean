/-
BP_IV §1.6 — Step 18b, density = series (the squeeze) + the movement
capstone (`DensityTie.lean`).
Units in this file: SKEL (module skeleton), D1 (`dmass_eq_sliceSum`, cast of
the PROVED corpus `TreeSeam.finiteness_stack`).  Later waves add
D0a (`dmass` monotone), D0 (`cylDensity`), D2 (`sum_cylDensity_eq_one`),
D3 (`cylDensity_eq_seriesSum`), D5 (`renewal_unique_of_margin`), and D4
(`valueSide_massTie`, the movement CAPSTONE).
Import graph (BP_IV §1.0/§4): this module imports the completed
`SeriesTie.lean`; `SeriesTie.lean` never imports this module.
-/
import Mathlib
import LeanUrat.Scaffold.ValueSide.SeriesTie

/-!
# Density = series + the value-side capstone [BP_IV division, unit SKEL]

**PROVENANCE (unit SKEL; BP_IV §1.6, module map §0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.6 (statement layer) and §0
  (module map row `DensityTie.lean` | step 18b | "squeeze +
  `valueSide_massTie`").
* Math source of record: the D-11 second tranche (MASS-ID M2, monic scope),
  per BP_IV §0 step-18b row.
* Imports: `Mathlib` + `LeanUrat.Scaffold.ValueSide.SeriesTie` (the §1.0
  acyclicity edge: DensityTie imports SeriesTie, never conversely;
  `BridgeKernels`/`DefsLedger` corpus vocabulary arrives transitively).
-/

namespace LeanUrat.Scaffold

open LeanUrat.MovesU ENNReal

/-- D1 (slice identity — REUSE, not re-proof; BP_IV §1.6): dmass σ N = slice
    sum, i.e. the corpus `TreeSeam.finiteness_stack`
    (`MovesU/DefsLedger.lean:249`, PROVED) recast over ℝ — divide the ℝ≥0∞
    partition identity decided_σ(N) = p^{nN} · Σ_{thr(T) ≤ N} μ(fiber T) by
    p^{nN} and take `toReal`. -/
theorem dmass_eq_sliceSum {n p : ℕ} [NeZero p] {X : ClassifierSpec n p}
    {F : FiberSeries n p X} (seam : TreeSeam n p X F)
    (σ : SplittingType n) (N : ℕ) :
    X.dmass σ N = (∑ T ∈ F.thrSlice σ N, F.mass σ T).toReal := by
  have h := seam.finiteness_stack σ N
  have hp0 : ((p : ℝ≥0∞)) ^ (n * N) ≠ 0 :=
    pow_ne_zero _ (Nat.cast_ne_zero.mpr (NeZero.ne p))
  have hpt : ((p : ℝ≥0∞)) ^ (n * N) ≠ ⊤ :=
    ENNReal.pow_ne_top (ENNReal.natCast_ne_top p)
  have hS : ∑ T ∈ F.thrSlice σ N, F.mass σ T
      = (X.decided σ N : ℝ≥0∞) / (p : ℝ≥0∞) ^ (n * N) := by
    rw [ENNReal.eq_div_iff hp0 hpt]
    exact h.symm
  rw [ClassifierSpec.dmass, hS, ENNReal.toReal_div]
  simp [ENNReal.toReal_pow]

end LeanUrat.Scaffold
