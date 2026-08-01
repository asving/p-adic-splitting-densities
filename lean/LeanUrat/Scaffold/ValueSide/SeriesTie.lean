/-
BP_IV §1.5 — Step 18, the resummation core + the tie assembly
(`SeriesTie.lean`).
Units in this file: SKEL (module skeleton) · S0 (seriesSum = ⨆ of slice sums —
located HERE so this file never depends on `DensityTie.lean`; REV-2 finding 5).
Later waves add S1a/S1b (Neumann sum + leastness), S2a/S2b
(`seriesSum_eq_lfp`), S3a/S3b (Bekić), S4a–S4c (margin/summability/solve
agreement), and S5 (`seriesTie_of_kernels`, targeting the corpus row
`BridgeKernels.series_tie`).
Import graph (BP_IV §1.0/§4): this module NEVER imports `DensityTie.lean`;
`DensityTie.lean` imports the completed `SeriesTie.lean`.
-/
import Mathlib
import LeanUrat.MovesU.BridgeKernels

/-!
# The resummation core + the series tie [BP_IV division, unit SKEL]

**PROVENANCE (unit SKEL; BP_IV §1.5, module map §0).**

* Blueprint: `lean/blueprints/BP_IV.md` §1.5 (statement layer) and §0
  (module map row `SeriesTie.lean` | step 18 | "resummation core +
  `seriesTie_of_kernels`").
* Math source of record: M04 (abstract resummation: lfp/Bekić/Neumann) +
  the O-11 r3 brief, per BP_IV §0 step-18 row.
* Imports: `Mathlib` + `LeanUrat.MovesU.BridgeKernels` (THE TARGET ROW
  `BridgeKernels.series_tie`, §3 corpus-reuse map; transitively supplies
  `FiberSeries`, `SolveSeam`, `TreeSeam` from `DefsLedger`).
-/

namespace LeanUrat.Scaffold

/-!
## Unit S0 — seriesSum is the supremum of the slice sums

**PROVENANCE (unit S0; BP_IV §2 S/D tables, S0 rows + §1.6 D3a note).**

* Blueprint statement (S-table row): "seriesSum is the supremum of slice
  sums"; (D-table row): "seriesSum σ = ⨆_N slice sums, located in
  `SeriesTie.lean`"; §1.6 D3a note: "seriesSum σ = ⨆ N (slice sum) (M04
  Thm 1, an interface lemma over `mem_slice_iff`)".  The level-N slice sum
  is the corpus partial sum `∑ T ∈ F.thrSlice σ N, F.mass σ T` (the same
  Finset sum as `MovesU.tonelli_partial_le` and D1's `TreeSeam` read).
* Math source of record: M04 Theorem 1 (the ⨆-characterization of the
  extended-value series sum).
* Proof per the S0 row sketch: `mem_slice_iff` makes the slices monotone
  and cofinal among Finsets (any Finset of trees sits inside the slice at
  N = its `thr`-sup), so the ℝ≥0∞ law "iSup of Finset sums along a cofinal
  family = tsum" (`ENNReal.tsum_eq_iSup_sum'`) applies.
* Location discipline (REV-2 finding 5): S0 lives HERE; this module never
  imports `DensityTie.lean` (D3 imports S0 from here).
-/

/-- S0 helper (the "«mem_slice_iff» monotone slices" half of the row sketch;
    the corpus-reuse map's `slice_mono` slot): the thr ≤ N slices grow
    monotonically in N. -/
theorem slice_mono {n p : ℕ} {X : MovesU.ClassifierSpec n p}
    (F : MovesU.FiberSeries n p X) (σ : MovesU.SplittingType n)
    {N M : ℕ} (h : N ≤ M) :
    F.thrSlice σ N ⊆ F.thrSlice σ M := fun T hT =>
  (F.mem_slice_iff σ M T).mpr (le_trans ((F.mem_slice_iff σ N T).mp hT) h)

/-- **S0** (M04 Theorem 1; BP_IV §2 S/D tables S0 rows + §1.6 D3a note):
    the extended-value series sum of the σ tree-fiber series is the supremum
    over N of the level-N slice sums.  Proof: the slices are cofinal among
    Finsets of trees — any Finset `t` is contained in the slice at
    `t.sup (F.thr σ)` by `mem_slice_iff` — so the ℝ≥0∞ tsum-as-iSup law
    along the family applies. -/
theorem seriesSum_eq_iSup_slice {n p : ℕ} {X : MovesU.ClassifierSpec n p}
    (F : MovesU.FiberSeries n p X) (σ : MovesU.SplittingType n) :
    F.seriesSum σ = ⨆ N, ∑ T ∈ F.thrSlice σ N, F.mass σ T :=
  ENNReal.tsum_eq_iSup_sum' (F.thrSlice σ) fun t =>
    ⟨t.sup (F.thr σ), fun T hT => (F.mem_slice_iff σ _ T).mpr (Finset.le_sup hT)⟩

end LeanUrat.Scaffold
