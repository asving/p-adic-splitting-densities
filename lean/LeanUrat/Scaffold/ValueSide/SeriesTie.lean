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

/-!
## Unit S3a — Bekić 2×2 block: prefix independence of the Neumann sum

**PROVENANCE (unit S3a; BP_IV §2 S-table row S3a + §1.5 statement layer).**

* Blueprint statement: `neumannSum_blockTriangular` + the `prefixMatrix` /
  `prefixVector` defs, VERBATIM from §1.5.  Math source of record: M04
  Lemma 3.2 (Bekić/triangular prefix independence).
* Deps S1a/S1b: the §1.5 `neumannSum` def (S1a's) is transcribed here
  VERBATIM since that unit has not landed in this file yet; if S1a lands
  its own copy, dedup keeps exactly this text.
* Proof: induction on the power N — for rows i < k, block triangularity
  makes `(A ^ N) i j` agree with the prefix power (and vanish for j ≥ k),
  so every Neumann summand agrees pointwise and `tsum_congr` closes.
-/

open scoped ENNReal

/-- S1a def (BP_IV §1.5 VERBATIM; transcribed here as S3a's dependency):
    the Neumann sum `Σ_k A^k b` in `(ℝ≥0∞)^m`. -/
noncomputable def neumannSum {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (b : Fin m → ℝ≥0∞) : Fin m → ℝ≥0∞ := fun i => ∑' k, (A ^ k).mulVec b i

/-- S3 prefix truncation of the kernel matrix (BP_IV §1.5 VERBATIM). -/
noncomputable def prefixMatrix {m : ℕ} (k : ℕ)
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) : Matrix (Fin m) (Fin m) ℝ≥0∞ :=
  fun i j => if i.1 < k ∧ j.1 < k then A i j else 0

/-- S3 prefix truncation of the entrance vector (BP_IV §1.5 VERBATIM). -/
noncomputable def prefixVector {m : ℕ} (k : ℕ)
    (b : Fin m → ℝ≥0∞) : Fin m → ℝ≥0∞ :=
  fun i => if i.1 < k then b i else 0

/-- S3a core induction (M04 Lemma 3.2 engine): on rows `i < k` of a
    block-triangular `A`, the N-th power agrees entrywise with the N-th
    power of the prefix truncation, and its `j ≥ k` entries vanish. -/
theorem pow_prefixMatrix_agree {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (htri : ∀ i j, i.1 < k → k ≤ j.1 → A i j = 0) :
    ∀ (N : ℕ) (i j : Fin m), i.1 < k →
      (A ^ N) i j = ((prefixMatrix k A) ^ N) i j
        ∧ (k ≤ j.1 → (A ^ N) i j = 0) := by
  intro N
  induction N with
  | zero =>
    intro i j hi
    refine ⟨rfl, fun hj => ?_⟩
    have hne : i ≠ j := fun h => (not_lt.mpr hj) (h ▸ hi)
    simp [pow_zero, Matrix.one_apply_ne hne]
  | succ N ih =>
    intro i j hi
    constructor
    · rw [pow_succ', pow_succ', Matrix.mul_apply, Matrix.mul_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : l.1 < k
      · have h1 : prefixMatrix k A i l = A i l := if_pos ⟨hi, hl⟩
        rw [h1, (ih l j hl).1]
      · have h0 : A i l = 0 := htri i l hi (not_lt.mp hl)
        have h0' : prefixMatrix k A i l = 0 := if_neg fun h => hl h.2
        rw [h0, h0', zero_mul, zero_mul]
    · intro hj
      rw [pow_succ', Matrix.mul_apply]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : l.1 < k
      · rw [(ih l j hl).2 hj, mul_zero]
      · rw [htri i l hi (not_lt.mp hl), zero_mul]

/-- **S3a** (Bekić 2×2 block, M04 Lemma 3.2; BP_IV §1.5 VERBATIM): on a
    block-triangular kernel the Neumann sum restricted to the first `k`
    states equals the Neumann sum of the prefix-truncated system. -/
theorem neumannSum_blockTriangular {m k : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (htri : ∀ i j, i.1 < k → k ≤ j.1 → A i j = 0) :
    ∀ i, i.1 < k →
      neumannSum A b i = neumannSum (prefixMatrix k A) (prefixVector k b) i := by
  intro i hi
  refine tsum_congr fun N => ?_
  show ∑ j, (A ^ N) i j * b j
      = ∑ j, ((prefixMatrix k A) ^ N) i j * prefixVector k b j
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j.1 < k
  · rw [(pow_prefixMatrix_agree A htri N i j hi).1]
    have hb : prefixVector k b j = b j := if_pos hj
    rw [hb]
  · rw [(pow_prefixMatrix_agree A htri N i j hi).2 (not_lt.mp hj)]
    have hb : prefixVector k b j = 0 := if_neg hj
    rw [hb, mul_zero, zero_mul]

/-!
## Unit S1b — leastness of the Neumann sum

**PROVENANCE (unit S1b; BP_IV §1.5 statement layer + §2 S-table row S1b).**

* Blueprint statement (§1.5, S1 block): `neumannSum_isLFP_least` below is
  the S1b (leastness) conjunct of the blueprint's `neumannSum_isLFP`,
  VERBATIM (`∀ y, y = b + A.mulVec y → neumannSum A b ≤ y`), over the
  §1.5 `neumannSum` carrier def transcribed VERBATIM above (S3a section;
  dedup per its note — S1b uses that single copy).
* S-table row S1b: "leastness | induction: partial sums ≤ any solution;
  `iSup` ≤ | dep S1a | MED | M04 Lemma 3.1".
* Math source of record: M04 Lemma 3.1 (leastness half).
* Assembly note: the S1a (solution) conjunct and the packaging of both
  conjuncts into `neumannSum_isLFP` belong to unit S1a (not yet landed in
  this file at S1b landing time).
-/

/-- S1b helper (kernel-action monotonicity): over ℝ≥0∞, `mulVec` is monotone
    in the vector argument (entrywise), since each entry is a finite sum of
    products with fixed left factors. -/
theorem mulVec_mono {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    {x y : Fin m → ℝ≥0∞} (h : x ≤ y) : A.mulVec x ≤ A.mulVec y := by
  intro i
  simp only [Matrix.mulVec, dotProduct]
  exact Finset.sum_le_sum fun j _ => mul_le_mul_left' (h j) (A i j)

/-- S1b helper (the row-sketch induction, "partial sums ≤ any solution"):
    every partial Neumann sum Σ_{k<N} A^k·b sits below any solution `y` of
    the affine recursion y = b + A·y.  Induction on N: the empty sum is 0;
    the (N+1)-sum reorganizes (`Finset.sum_range_succ'`) as
    b + A·(N-partial sum) ≤ b + A·y = y, by `mulVec_mono`. -/
theorem partialNeumann_le_solution {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ≥0∞}
    {b y : Fin m → ℝ≥0∞} (hy : y = b + A.mulVec y) (N : ℕ) :
    ∑ k ∈ Finset.range N, (A ^ k).mulVec b ≤ y := by
  induction N with
  | zero => simpa using zero_le y
  | succ N ih =>
    have hstep : ∑ k ∈ Finset.range (N + 1), (A ^ k).mulVec b
        = b + A.mulVec (∑ k ∈ Finset.range N, (A ^ k).mulVec b) := by
      rw [Finset.sum_range_succ', Matrix.mulVec_sum]
      simp only [pow_succ', pow_zero, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
      exact add_comm _ b
    calc ∑ k ∈ Finset.range (N + 1), (A ^ k).mulVec b
        = b + A.mulVec (∑ k ∈ Finset.range N, (A ^ k).mulVec b) := hstep
      _ ≤ b + A.mulVec y := add_le_add_left (mulVec_mono A ih) b
      _ = y := hy.symm

/-- **S1b** (M04 Lemma 3.1, leastness half; BP_IV §2 S-table row S1b — the
    second conjunct of §1.5's `neumannSum_isLFP`, VERBATIM): the Neumann sum
    is ≤ every solution of the affine recursion x = b + A·x in (ℝ≥0∞)^m.
    Proof per the row sketch: entrywise, the ℝ≥0∞ tsum is the `iSup` of the
    partial sums (`ENNReal.tsum_eq_iSup_nat`), each partial sum is ≤ y by
    `partialNeumann_le_solution`, and `iSup_le` closes. -/
theorem neumannSum_isLFP_least {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (b : Fin m → ℝ≥0∞) :
    ∀ y, y = b + A.mulVec y → neumannSum A b ≤ y := by
  intro y hy i
  show ∑' k, (A ^ k).mulVec b i ≤ y i
  rw [ENNReal.tsum_eq_iSup_nat]
  exact iSup_le fun N => by
    simpa using partialNeumann_le_solution hy N i

end LeanUrat.Scaffold
