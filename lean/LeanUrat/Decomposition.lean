/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Mathlib
import LeanUrat.Interface
import LeanUrat.RatFn
import LeanUrat.OMInduction
import LeanUrat.CountingModel
import LeanUrat.MontesAxiom

/-!
# LeanUrat.Decomposition — the decomposition theorem and rationality, modulo M1 (only-Montes footprint)

This module assembles `notes/DECOMP_BLUEPRINT.tex` §3 (Theorem `thm:decomp`) and §5 (Theorem
`thm:rational`) in the counting model:

* **`countingDensity σ = ∑_{T ∈ shapesOf σ} C_T(q)`** — the DECIDED-LIMIT density is a finite sum over
  the shape menu of the per-shape coefficients `C_T(q) := lim_N stratumCount T N / q^{nN}`. PROVED
  from M1 (`partition` + `nodeMultiplicativity`) by counting-additivity over the finite partition and
  the uniqueness of limits.
* **Rationality:** each `C_T(q)` is a uniform rational function of `q`. **As of 2026-06-20 this runs
  through the GENERIC OM engine `OMInduction.clusterVol_isRational` directly over `ClusterShape`** with
  the count-native `cells`/`treeSize`/`countCellCoeff`/`countPivot` — NO `PadicMeasure.clusterMeasure`,
  NO `PadicMeasure.AX_cellRecursion`. Hence the finite sum `countingDensity σ` is a uniform rational
  function of `q` (`RatFn.isRationalFn_listSum`).

## The only-Montes footprint (the 2026-06-20 push)

`C_T := MontesData.C` is the pure-counting recursion `clusterCount` (`T_BB3 × T_BB1 × ∏_children`,
self-loop geometric-summed). The rationality/decomposition path therefore depends ONLY on Lean core +
the M1 `MontesData` fields (`partition`, `nodeMultiplicativity` as the count factorization,
`cells`, `treeSize`, `cells_descend`, `finiteTermination`). There is NO `clusterMeasure`, NO
`AX_cellRecursion`, NO `PadicMeasure.omCells`, NO `PadicMeasure.descend_size_lt` in the footprint
(verified by `#print axioms`). This module no longer imports `LeanUrat.PadicMeasure`.

## Status

PROVED modulo M1 (the `MontesData` hypothesis):
* `coeff_eq_C` — `C_T = MontesData.C` (definitional).
* `coeff_isRational` — PROVED via the GENERIC engine over `ClusterShape` (no measure layer).
* `countingDensity_isRational` — PROVED from `coeff_isRational` + finite-sum closure.
* `countingDensity_eq_sum_coeff` — the limit-interchange proof (M1 `nodeMultiplicativity` +
  `partition`). No rationality assumed.

## The standing measure wall (un-constructed `CountingModel`/`MontesData`)

The whole counting path is a THEOREM *modulo* the hypotheses `M : CountingModel` and `D : MontesData M`.
Constructing these from actual `O_K/p^N` enumeration needs a `p`-adic measure/enumeration foundation
absent in mathlib v4.31.0. This is the honest interpretive boundary: "sorry-free modulo M1+core" ≠
"the p-adic theorem is unconditionally formalized." It does not appear in `#print axioms` (it is a
hypothesis, not an axiom).
-/

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false

namespace LeanUrat.MontesAxiom.MontesData

open LeanUrat CountingModel MontesAxiom RatFn Filter Topology

variable {q n : ℕ} {M : CountingModel q n} (D : MontesData q n M)

/-- **The per-shape coefficient `C_T(q) := MontesData.C` — the pure-counting per-node factorization.**
This is the recursively-DEFINED count factorization `(T_BB3 residual count) × (T_BB1 box count) ×
∏_children`, the self-loop geometric-summed (`MontesData.C`), NOT the old opaque `clusterMeasure`. By
M1's `nodeMultiplicativity`, it is the genuine `lim_N stratumCount T N / q^{nN}`. -/
noncomputable def coeff (T : ClusterShape) (q : ℕ) : ℚ :=
  D.C T q

/-- **`C_T = MontesData.C`** (definitional). -/
theorem coeff_eq_C (T : ClusterShape) (q' : ℕ) : D.coeff T q' = D.C T q' := rfl

/-- **The shape stratum measure converges to `C_T`** (M1 `nodeMultiplicativity`, restated through
`coeff`). The normalized stratum count `stratumCount T N / q^{nN}` tends to `C_T(q)`. PROVED (= M1
field, via `stratum_tendsto_C`). -/
theorem stratum_tendsto_coeff (T : ClusterShape) :
    Tendsto (fun N => D.stratumCount T N / (q : ℚ) ^ (n * N)) atTop (nhds (D.coeff T q)) :=
  D.stratum_tendsto_C T

/-! ### The decomposition theorem (`thm:decomp`) -/

/-- **`decidedMeasure σ N = ∑_{T ∈ shapesOf σ} stratumCount T N / q^{nN}`** — counting-additivity over
the finite partition at each level `N` (M1 `partition`, divided by the box `q^{nN}`). PROVED. -/
theorem decidedMeasure_eq_sum (σ : FactorizationType) (N : ℕ) :
    M.decidedMeasure σ N = ∑ T ∈ D.shapesOf σ, D.stratumCount T N / (q : ℚ) ^ (n * N) := by
  unfold CountingModel.decidedMeasure
  rw [D.partition σ N, Finset.sum_div]

/-- **DECOMPOSITION THEOREM (`thm:decomp`): `countingDensity σ = ∑_{T ∈ shapesOf σ} C_T(q)`.**

The DECIDED-LIMIT density is the finite sum over the shape menu of the per-shape coefficients. PROVED
modulo M1:
* at each `N`, `decidedMeasure σ N = ∑_T (stratumCount T N / q^{nN})` (M1 `partition`);
* each summand `→ C_T` (M1 `nodeMultiplicativity`, `stratum_tendsto_coeff`), so the FINITE sum
  `→ ∑_T C_T`;
* but `decidedMeasure σ N → countingDensity σ` (`CountingModel.density_isLimit`);
* limits are unique, so `countingDensity σ = ∑_T C_T`.

The left side is the genuine density (the decided limit), the right side is the OM tree-sum; this is
the blueprint's `ρ = ∑_T C_T`, a theorem, not a definitional tautology. No rationality is used. -/
theorem countingDensity_eq_sum_coeff (σ : FactorizationType) :
    M.countingDensity σ = ∑ T ∈ D.shapesOf σ, D.coeff T q := by
  have hN : (fun N => M.decidedMeasure σ N)
      = (fun N => ∑ T ∈ D.shapesOf σ, D.stratumCount T N / (q : ℚ) ^ (n * N)) := by
    funext N; exact D.decidedMeasure_eq_sum σ N
  have hsum_tendsto :
      Tendsto (fun N => ∑ T ∈ D.shapesOf σ, D.stratumCount T N / (q : ℚ) ^ (n * N)) atTop
        (nhds (∑ T ∈ D.shapesOf σ, D.coeff T q)) :=
    tendsto_finsetSum (D.shapesOf σ) (fun T _ => D.stratum_tendsto_coeff T)
  have hdec_tendsto :
      Tendsto (fun N => M.decidedMeasure σ N) atTop (nhds (∑ T ∈ D.shapesOf σ, D.coeff T q)) := by
    rw [hN]; exact hsum_tendsto
  exact tendsto_nhds_unique (M.density_isLimit σ) hdec_tendsto

/-! ### Rationality (`thm:rational`) — through the GENERIC OM engine over `ClusterShape` -/

/-- **Each per-shape coefficient `C_T` is a uniform rational function of `q`** (`thm:rational`).

`C_T = MontesData.C` is the pure-counting `clusterCount` recursion. Its rationality is DERIVED by the
GENERIC OM-order induction `OMInduction.clusterVol_isRational` instantiated directly over
`ClusterShape` with the count-native data:
* `size := D.treeSize`, `clusterVol := D.C`;
* `contribs T := (D.cells T).map (c ↦ (countCellCoeff c, c.children))` — one entry per count cell;
* `pivot T := countPivot (D.treeSize T)`;
* `hrec` := the `C_rec` recursion-unfold (rewriting `contribs`/`countCellCoeff` — pure list rewriting);
* `hdescend` := `D.cells_descend` (M1 strict-descent field);
* `hcoeff` := `countCellCoeff_isRational` (`T_BB3` residual count × `T_BB1` box, both rational);
* `hpivot_rat`/`hpivot_ne` := `countPivot_isRational`/`countPivot_ne` (← `L5fix.selfLoop_geometric`).

**NO `PadicMeasure.clusterMeasure`, NO `AX_cellRecursion`, NO `omCells`, NO `descend_size_lt`.** The
footprint is `[core]` + the M1 fields. PROVED. -/
theorem coeff_isRational (T : ClusterShape) : IsRationalFn (D.coeff T) := by
  have hgen := OMInduction.clusterVol_isRational
    (Shape := ClusterShape)
    (size := D.treeSize)
    (clusterVol := D.C)
    (contribs := fun T => (D.cells T).map (fun c => (countCellCoeff c, c.children)))
    (pivot := fun T => countPivot (D.treeSize T))
    ?hrec ?hdescend ?hcoeff ?hpivot_rat ?hpivot_ne T
  · -- transport `IsRationalFn (D.C T)` to `IsRationalFn (D.coeff T)` (definitionally equal)
    exact hgen
  case hrec =>
    -- the `C_rec` recursion-unfold, with `contribs`/`countCellCoeff` rewritten into engine shape.
    intro T q hq
    rw [D.C_rec T q]
    congr 1            -- peel `_ / countPivot _ q`
    congr 1            -- peel `(_).sum`
    -- the cell-map equals the contribution-map: fuse `(g ∘ (c ↦ (coeff, children)))` and match.
    rw [List.map_map]
    apply List.map_congr_left
    intro c _
    simp only [Function.comp_apply]
  case hdescend =>
    -- every contribution child is a cell child, strictly smaller by `cells_descend`.
    intro T c hc ch hch
    simp only [List.mem_map] at hc
    obtain ⟨cell, hcell_mem, hc_eq⟩ := hc
    rw [← hc_eq] at hch
    exact D.cells_descend T cell hcell_mem ch hch
  case hcoeff =>
    -- each contribution coefficient is `countCellCoeff cell`, rational.
    intro T c hc
    simp only [List.mem_map] at hc
    obtain ⟨cell, _, hc_eq⟩ := hc
    rw [← hc_eq]
    exact countCellCoeff_isRational cell
  case hpivot_rat =>
    intro T
    exact countPivot_isRational (D.treeSize T)
  case hpivot_ne =>
    intro T q hq
    exact countPivot_ne (D.treeSize T) q hq

/-- **RATIONALITY THEOREM (`thm:rational`): `countingDensity σ` is a uniform rational function of
`q`.** It is the finite sum `∑_{T ∈ shapesOf σ} C_T(q)` (the decomposition theorem), each `C_T`
rational (`coeff_isRational`), and `IsRationalFn` is closed under finite sums
(`RatFn.isRationalFn_listSum`). PROVED modulo M1, with the only-Montes footprint.

Honest scope: this proves rationality of the function `q ↦ ∑_T coeff T q` AS A FUNCTION OF `q`; the
decomposition theorem ties `countingDensity σ` (at this `M`'s `q`) to the value of that rational
function at `q`. -/
theorem countingDensity_isRational (σ : FactorizationType) :
    IsRationalFn (fun q' => ∑ T ∈ D.shapesOf σ, D.coeff T q') := by
  classical
  set L : List (ℕ → ℚ) := (D.shapesOf σ).toList.map (fun T => D.coeff T) with hL
  have hLrat : ∀ f ∈ L, IsRationalFn f := by
    intro f hf
    rw [hL, List.mem_map] at hf
    obtain ⟨T, _, rfl⟩ := hf
    exact D.coeff_isRational T
  have hlist : IsRationalFn (fun q' => (L.map (fun f => f q')).sum) :=
    RatFn.isRationalFn_listSum L hLrat
  have heq : (fun q' => (L.map (fun f => f q')).sum)
      = (fun q' => ∑ T ∈ D.shapesOf σ, D.coeff T q') := by
    funext q'
    rw [hL, List.map_map]
    exact Finset.sum_map_toList (D.shapesOf σ) (fun T => D.coeff T q')
  rwa [heq] at hlist

end LeanUrat.MontesAxiom.MontesData

namespace LeanUrat.Decomposition

/-! ### Wiring assessment (NOT a rewire) -/

/-- **Wiring assessment (a statement-level record, deliberately trivial-bodied).**

This `True` proposition's docstring records the assessment of how the counting-model theorems above
relate to the ASSUMED interface fields.

* `Interface.DensityFoundation.decomposition` (ASSUMED: `density = ∑_T m_T · clusterVolume T`) would be
  DERIVED by `countingDensity_eq_sum_coeff` (`countingDensity σ = ∑_T C_T`), once `F.density` is
  identified with `M.countingDensity` and `F.clusterVolume T` with `coeff T`.
* **The 2026-06-20 push eliminated the measure layer from THIS path.** `coeff := MontesData.C` is the
  pure-counting recursion; `coeff_isRational` runs through the GENERIC `OMInduction.clusterVol_isRational`
  over `ClusterShape` with `cells`/`treeSize`/`countCellCoeff`/`countPivot`. So the rationality/
  decomposition footprint is `{Lean core} ∪ {M1 MontesData fields}` — verified by `#print axioms` to
  carry NO `clusterMeasure`, NO `AX_cellRecursion`, NO `PadicMeasure.omCells`, NO `descend_size_lt`.
* **Gap that blocks a full rewire of `Goal`/`Interface.DensityFoundation`:** identifying `F.density n σ q`
  with `M.countingDensity σ` needs a `CountingModel` whose `decidedCount` is the genuine `p`-adic coset
  count and whose `densityVal`/`decided_tendsto` is the genuine Haar limit — the un-constructed measure
  foundation (mathlib v4.31.0 has no `p`-adic Haar measure). `Goal.goal_theorem` still routes its
  density through `Interface.DensityFoundation.clusterVolume_eq_measure := clusterMeasure (decode T)`,
  so it STILL carries `clusterMeasure`/`AX_cellRecursion`/`omCells`/`descend_size_lt` (and
  `tame_functionalEquation` for the palindromy half). Re-pointing the interface at `MontesData.C` is a
  follow-on plumbing step resting on the same measure wall. -/
theorem wiring_assessment : True := trivial

end LeanUrat.Decomposition
