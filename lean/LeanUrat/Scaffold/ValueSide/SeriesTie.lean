/-
BP_IV §1.5 — Step 18, the resummation core + the tie assembly
(`SeriesTie.lean`).
Units in this file: SKEL (module skeleton) · S0 (seriesSum = ⨆ of slice sums —
located HERE so this file never depends on `DensityTie.lean`; REV-2 finding 5)
· S3a (Bekić block, with the §1.5-verbatim `neumannSum` def) · S3b1 (full
triangularization, the one-block induction step) · S1b (leastness)
· S1a (solution half + `neumannSum_isLFP`) · S4a (summability from the
row-sum margin — the power bound, geometric comparison, and finiteness)
· S4b (the §1.5-verbatim parent `neumann_eq_solve_of_margin`: toReal of the
Neumann sum agrees with every real affine solution under the margin).
· S2b (`seriesSum_eq_lfp`, with the `TreeRecursion` carrier and the S2a
slice identity transcribed as its dependencies — see that section's
deviation record on the carrier's `: Prop` ascription)
· S4c1 (finite evaluation: the Neumann value = the Cramer/matrix solve
`(1 − A_ℝ)⁻¹ · b_ℝ`, invertibility as the explicit M4-shaped `hdet` binder).
· S5a (state/block reindexing)
· S4c2 (SolveSeam agreement — the tie to `SolveSeam.r_is_solve`'s `Rsh`
under RegP, the evalℝ/Rval read of the margin evaluation)
· S5b (`seriesTie_of_kernels` + its named pricing row `SolvePricing`,
LANDED at REVISION 3 — targeting the corpus row `BridgeKernels.series_tie`;
the original probe obstruction record and the mop-up adjudication are in the
S5b section).  S3b2 is retired at REVISION 3: the §1.5-displayed S3 statement
`neumannSum_blockTriangular` is landed and PROVED above (direct proof), and
its chained form `neumannSum_blockTriangular_step` covers the multi-block
passage — no residual obligation.
Import graph (BP_IV §1.0/§4): this module NEVER imports `DensityTie.lean`;
`DensityTie.lean` imports the completed `SeriesTie.lean`.  REVISION 3 adds
the `Census.lean` import (the census/ADM rows S5b binds), exactly the edge
the Census.lean header already records ("imported by the repaired
SeriesTie.lean/DensityTie.lean").
-/
import Mathlib
import LeanUrat.MovesU.BridgeKernels
import LeanUrat.Scaffold.ValueSide.Census

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
## Unit S3b1 — full triangularization: the one-block induction step

**PROVENANCE (unit S3b1; BP_IV §2 S-table row S3b, first split per §4
wave 3: S3a → S3b1 (one induction step) → S3b2).**

* Parent target (§1.5 VERBATIM): `neumannSum_blockTriangular` — landed and
  proved ABOVE (S3a section; re-verified byte-identical to the §1.5
  display at S3b1 landing; dedup keeps that single copy).
* S-table row S3b: "full triangularization | induction on blocks via S3a
  | dep S3a | MED | M04 Lemma 3.2".  S3b1 contributes ONE step of the
  block induction (M04's bottom-up Bekić passage, Lemma 3.2's
  "lfp = bottom-up composition of per-block lfps"): descending one cut in
  a nested pair k ≤ k', the k'-prefix system's Neumann sum agrees on rows
  i < k with the k-prefix system's.  S3b2 chains these steps along a
  block filtration into the full-triangularization statement.
* Proof per the row sketch ("via S3a"): the k'-truncated kernel inherits
  the cut-k triangularity (`prefixMatrix_blockTriangular`), so S3a's
  `neumannSum_blockTriangular` applies AT the truncated system; the
  nested truncations then collapse to the smaller cut
  (`prefixMatrix_prefixMatrix` / `prefixVector_prefixVector`).
-/

/-- S3b1 helper (inherited triangularity): a kernel block-triangular at
    cut k stays block-triangular at cut k after any prefix truncation. -/
theorem prefixMatrix_blockTriangular {m k k' : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (htri : ∀ i j, i.1 < k → k ≤ j.1 → A i j = 0) :
    ∀ i j, i.1 < k → k ≤ j.1 → prefixMatrix k' A i j = 0 := by
  intro i j hi hj
  by_cases h : i.1 < k' ∧ j.1 < k'
  · show (if i.1 < k' ∧ j.1 < k' then A i j else 0) = 0
    rw [if_pos h]
    exact htri i j hi hj
  · exact if_neg h

/-- S3b1 helper (truncation composition, kernel leg): nested prefix
    truncations collapse to the smaller cut. -/
theorem prefixMatrix_prefixMatrix {m k k' : ℕ} (hkk' : k ≤ k')
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) :
    prefixMatrix k (prefixMatrix k' A) = prefixMatrix k A := by
  funext i j
  show (if i.1 < k ∧ j.1 < k then prefixMatrix k' A i j else 0)
      = if i.1 < k ∧ j.1 < k then A i j else 0
  by_cases h : i.1 < k ∧ j.1 < k
  · rw [if_pos h, if_pos h]
    exact if_pos ⟨h.1.trans_le hkk', h.2.trans_le hkk'⟩
  · rw [if_neg h, if_neg h]

/-- S3b1 helper (truncation composition, entrance leg). -/
theorem prefixVector_prefixVector {m k k' : ℕ} (hkk' : k ≤ k')
    (b : Fin m → ℝ≥0∞) :
    prefixVector k (prefixVector k' b) = prefixVector k b := by
  funext i
  show (if i.1 < k then prefixVector k' b i else 0)
      = if i.1 < k then b i else 0
  by_cases h : i.1 < k
  · rw [if_pos h, if_pos h]
    exact if_pos (h.trans_le hkk')
  · rw [if_neg h, if_neg h]

/-- **S3b1** (M04 Lemma 3.2, one step of the block induction; BP_IV §4
    wave-3 first split of S-table row S3b): descending one cut in a block
    filtration — for nested cuts k ≤ k' and a kernel block-triangular at
    the smaller cut k, the Neumann sum of the k'-prefix system agrees on
    rows i < k with the Neumann sum of the k-prefix system.  Proof per the
    row sketch: S3a (`neumannSum_blockTriangular`, the §1.5-verbatim
    parent, proved above) applied at the k'-truncated system, then the
    nested truncations collapse by the composition helpers. -/
theorem neumannSum_blockTriangular_step {m k k' : ℕ} (hkk' : k ≤ k')
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (htri : ∀ i j, i.1 < k → k ≤ j.1 → A i j = 0) :
    ∀ i, i.1 < k →
      neumannSum (prefixMatrix k' A) (prefixVector k' b) i
        = neumannSum (prefixMatrix k A) (prefixVector k b) i := by
  intro i hi
  rw [neumannSum_blockTriangular (prefixMatrix k' A) (prefixVector k' b)
      (prefixMatrix_blockTriangular A htri) i hi,
    prefixMatrix_prefixMatrix hkk', prefixVector_prefixVector hkk']

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
  exact Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (h j)

/-- S1b helper (the row-sketch induction, "partial sums ≤ any solution"):
    every partial Neumann sum Σ_{k<N} A^k·b sits below any solution `y` of
    the affine recursion y = b + A·y.  Induction on N: the empty sum is 0;
    the (N+1)-sum reorganizes (`Finset.sum_range_succ'`) as
    b + A·(N-partial sum) ≤ b + A·y = y, by `mulVec_mono`. -/
theorem partialNeumann_le_solution {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ≥0∞}
    {b y : Fin m → ℝ≥0∞} (hy : y = b + A.mulVec y) (N : ℕ) :
    ∑ k ∈ Finset.range N, (A ^ k).mulVec b ≤ y := by
  induction N with
  | zero => simp
  | succ N ih =>
    have hstep : ∑ k ∈ Finset.range (N + 1), (A ^ k).mulVec b
        = b + A.mulVec (∑ k ∈ Finset.range N, (A ^ k).mulVec b) := by
      rw [Finset.sum_range_succ', Matrix.mulVec_sum]
      simp only [pow_succ', pow_zero, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
      exact add_comm _ b
    calc ∑ k ∈ Finset.range (N + 1), (A ^ k).mulVec b
        = b + A.mulVec (∑ k ∈ Finset.range N, (A ^ k).mulVec b) := hstep
      _ ≤ b + A.mulVec y := add_le_add le_rfl (mulVec_mono A ih)
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

/-!
## Unit S1a — the solution half of `neumannSum_isLFP` + the packaging

**PROVENANCE (unit S1a; BP_IV §1.5 S1 block + §2 S-table row S1a).**

* Blueprint statement (§1.5, S1 block, VERBATIM): the `neumannSum` def
  (single copy kept above, S3a section, per that unit's dedup note — S1a
  adds no second one) and the theorem `neumannSum_isLFP` below (both
  conjuncts exactly as displayed in §1.5).
* S-table row S1a: "`neumannSum` solves x = b + A·x | ℝ≥0∞ tsum shift
  Σ_k A^{k+1}b = A·Σ A^k b (ENNReal.tsum commutes with mulVec — finite
  sums)".
* Math source of record: M04 Lemma 3.1 (half 1: the Neumann sum solves the
  affine recursion x = b + A·x in (ℝ≥0∞)^m).
* Serial split (BP_IV §2/§5: S1a → S1b): S1a supplies the SOLUTION conjunct
  (`neumannSum_solves`) and packages `neumannSum_isLFP` from it together
  with S1b's leastness conjunct (`neumannSum_isLFP_least`, landed above).
-/

/-- S1a helper (the "ENNReal.tsum commutes with mulVec" leg of the row
    sketch): `mulVec` is a finite sum per coordinate, so it commutes with
    an ℕ-indexed `tsum` in `ℝ≥0∞` — pull the scalar inside each summand by
    `ENNReal.tsum_mul_left`, then swap the Finset sum with the tsum
    (`Summable.tsum_finsetSum`; everything is summable in `ℝ≥0∞`). -/
theorem mulVec_tsum {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (v : ℕ → Fin m → ℝ≥0∞) (i : Fin m) :
    A.mulVec (fun j => ∑' k, v k j) i = ∑' k, A.mulVec (v k) i := by
  simp only [Matrix.mulVec, dotProduct]
  calc ∑ j, A i j * ∑' k, v k j
      = ∑ j, ∑' k, A i j * v k j := by simp_rw [ENNReal.tsum_mul_left]
    _ = ∑' k, ∑ j, A i j * v k j :=
        (Summable.tsum_finsetSum fun j _ => ENNReal.summable).symm

/-- **S1a** (M04 Lemma 3.1 half 1, solution leg; BP_IV §2 S-table row S1a):
    the Neumann sum solves x = b + A·x.  Proof per the row sketch: peel the
    k = 0 term of the `ℝ≥0∞` tsum (`tsum_eq_zero_add'`, unconditional
    summability), rewrite `A^{k+1} b = A·(A^k b)` (`pow_succ'` +
    `Matrix.mulVec_mulVec`), then pull the tsum through `mulVec` by
    `mulVec_tsum`. -/
theorem neumannSum_solves {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (b : Fin m → ℝ≥0∞) :
    neumannSum A b = b + A.mulVec (neumannSum A b) := by
  funext i
  calc neumannSum A b i
      = (A ^ 0).mulVec b i + ∑' k, (A ^ (k + 1)).mulVec b i :=
        tsum_eq_zero_add' ENNReal.summable
    _ = b i + ∑' k, A.mulVec ((A ^ k).mulVec b) i := by
        simp only [pow_zero, Matrix.one_mulVec, pow_succ', ← Matrix.mulVec_mulVec]
    _ = b i + A.mulVec (neumannSum A b) i :=
        congrArg (b i + ·) (mulVec_tsum A (fun k => (A ^ k).mulVec b) i).symm
    _ = (b + A.mulVec (neumannSum A b)) i := rfl

/-- S1 (M04 Lemma 3.1 half 1): the Neumann sum solves the affine recursion
    x = b + A·x and is its LEAST solution in (ℝ≥0∞)^m (S1a: solution;
    S1b: leastness by induction on partial sums). -/
theorem neumannSum_isLFP {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (b : Fin m → ℝ≥0∞) :
    neumannSum A b = b + A.mulVec (neumannSum A b)
    ∧ ∀ y, y = b + A.mulVec y → neumannSum A b ≤ y :=
  ⟨neumannSum_solves A b, neumannSum_isLFP_least A b⟩

/-!
## Unit S4a — summability from the row-sum margin

**PROVENANCE (unit S4a; BP_IV §2 S-table row S4a + §1.5 S4 block).**

* S-table row S4a: "summability from margin | row-sum ρ ≤ q₀^{1−E} ≤ 1/2
  (M3') ⇒ ‖A^k b‖ ≤ 2^{−k}‖b‖; comparison | dep M3' | MED | M04 Lemma 3.3".
* Parent statement (§1.5 S4 block, VERBATIM target of the S4 chain):
  `neumann_eq_solve_of_margin` — S4a's binders `(hfiniteA) (hfiniteb) (ρ)
  (hρ0) (hρ1) (hmargin)` are transcribed EXACTLY from that display, so
  S4b/S4c consume these lemmas without hypothesis adaptation.
* Math source of record: M04 Lemma 3.3 (geometric domination of the
  Neumann tail under a strict row-sum margin).
* Dep M3' (the margin input ρ ≤ q₀^{1−E} ≤ 1/2) stays an EXPLICIT
  hypothesis binder (`hmargin`; `hhalf` in the 2^{−k} display) — never an
  axiom, per the [M]-hypothesis discipline.
* The norm of the row sketch is realized as the total entrance mass
  `∑ j, b j` (equivalent to the sup norm within a factor m; the comparison
  test needs only SOME finite dominator, and total mass avoids an empty-
  `Fin 0` sup corner).
-/

/-- S4a step 0 (margin transport): under entrywise finiteness, the `toReal`
    row-sum margin of the parent display lifts to ℝ≥0∞ — every row of `A`
    sums to at most `ENNReal.ofReal ρ`. -/
theorem rowSum_le_ofReal_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ) :
    ∀ i, ∑ j, A i j ≤ ENNReal.ofReal ρ := by
  intro i
  have hne : (∑ j, A i j) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun j _ => (hfiniteA i j).lt_top).ne
  rw [ENNReal.le_ofReal_iff_toReal_le hne hρ0,
    ENNReal.toReal_sum fun j _ => hfiniteA i j]
  exact hmargin i

/-- S4a step 1 (the row-sketch power bound "‖A^k b‖ ≤ ρ^k·‖b‖", ℝ≥0∞ form):
    under the margin, every coordinate of `A^k·b` is at most `(ofReal ρ)^k`
    times the total entrance mass.  Induction on k: the base case is one
    summand of the total mass; the step peels one factor of `A`
    (`pow_succ'`/`mulVec_mulVec`) and prices its row by
    `rowSum_le_ofReal_of_margin`. -/
theorem pow_mulVec_le_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ) :
    ∀ (k : ℕ) (i : Fin m),
      (A ^ k).mulVec b i ≤ ENNReal.ofReal ρ ^ k * ∑ j, b j := by
  intro k
  induction k with
  | zero =>
    intro i
    simpa [Matrix.one_mulVec] using
      Finset.single_le_sum (f := b) (fun j _ => zero_le) (Finset.mem_univ i)
  | succ k ih =>
    intro i
    have hstep : (A ^ (k + 1)).mulVec b i
        = A.mulVec ((A ^ k).mulVec b) i := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [hstep]
    calc A.mulVec ((A ^ k).mulVec b) i
        = ∑ j, A i j * (A ^ k).mulVec b j := by
          simp [Matrix.mulVec, dotProduct]
      _ ≤ ∑ j, A i j * (ENNReal.ofReal ρ ^ k * ∑ j', b j') :=
          Finset.sum_le_sum fun j _ => mul_le_mul' le_rfl (ih j)
      _ = (∑ j, A i j) * (ENNReal.ofReal ρ ^ k * ∑ j', b j') :=
          (Finset.sum_mul ..).symm
      _ ≤ ENNReal.ofReal ρ * (ENNReal.ofReal ρ ^ k * ∑ j', b j') :=
          mul_le_mul'
            (rowSum_le_ofReal_of_margin A hfiniteA ρ hρ0 hmargin i) le_rfl
      _ = ENNReal.ofReal ρ ^ (k + 1) * ∑ j', b j' := by
          rw [pow_succ', mul_assoc]

/-- S4a display (the S-table row's literal 2^{−k} shape, at M3''s
    ρ ≤ 1/2): with margin at most one half, ‖A^k b‖ ≤ 2^{−k}·‖b‖ —
    coordinatewise, `(A^k·b)_i ≤ 2⁻¹^k · Σ_j b j`. -/
theorem pow_mulVec_le_two_pow_of_margin_half {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hhalf : ρ ≤ 1 / 2)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ) :
    ∀ (k : ℕ) (i : Fin m),
      (A ^ k).mulVec b i ≤ (2 : ℝ≥0∞)⁻¹ ^ k * ∑ j, b j := by
  intro k i
  refine (pow_mulVec_le_of_margin A b hfiniteA ρ hρ0 hmargin k i).trans
    (mul_le_mul' (pow_le_pow_left' ?_ k) le_rfl)
  calc ENNReal.ofReal ρ
      ≤ ENNReal.ofReal (1 / 2) := ENNReal.ofReal_le_ofReal hhalf
    _ = (2 : ℝ≥0∞)⁻¹ := by
        rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num,
          ENNReal.ofReal_inv_of_pos (by norm_num : (0 : ℝ) < 2),
          ENNReal.ofReal_ofNat]

/-- **S4a** (M04 Lemma 3.3, summability from margin — the comparison half;
    BP_IV §2 S-table row S4a): under the row-sum margin, the Neumann sum is
    dominated coordinatewise by the geometric value
    `(1 − ofReal ρ)⁻¹ · Σ_j b j`.  Proof: termwise comparison against the
    power bound, then `ENNReal.tsum_geometric` resummation (§3 corpus-reuse
    map row "geometric resummation" for this unit). -/
theorem neumannSum_le_geometric_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ) :
    ∀ i, neumannSum A b i ≤ (1 - ENNReal.ofReal ρ)⁻¹ * ∑ j, b j := by
  intro i
  calc neumannSum A b i
      = ∑' k, (A ^ k).mulVec b i := rfl
    _ ≤ ∑' k : ℕ, ENNReal.ofReal ρ ^ k * ∑ j, b j :=
        ENNReal.tsum_le_tsum fun k =>
          pow_mulVec_le_of_margin A b hfiniteA ρ hρ0 hmargin k i
    _ = (∑' k : ℕ, ENNReal.ofReal ρ ^ k) * ∑ j, b j := ENNReal.tsum_mul_right
    _ = (1 - ENNReal.ofReal ρ)⁻¹ * ∑ j, b j := by rw [ENNReal.tsum_geometric]

/-- **S4a finiteness** (the clause D5's row and S4b consume — "S4a's
    finiteness"): under the STRICT margin ρ < 1 with finite kernel and
    entrance data, every coordinate of the Neumann sum is finite.  Binders
    are exactly the parent `neumann_eq_solve_of_margin`'s (§1.5 VERBATIM
    display), minus the solution `x`. -/
theorem neumannSum_ne_top_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤) (hfiniteb : ∀ i, b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ) :
    ∀ i, neumannSum A b i ≠ ⊤ := by
  intro i
  have hb : (∑ j, b j) ≠ ⊤ :=
    (ENNReal.sum_lt_top.mpr fun j _ => (hfiniteb j).lt_top).ne
  have hρ' : ENNReal.ofReal ρ < 1 := ENNReal.ofReal_lt_one.mpr hρ1
  have hsub : (1 : ℝ≥0∞) - ENNReal.ofReal ρ ≠ 0 := by
    rw [Ne, tsub_eq_zero_iff_le]
    exact fun h => absurd hρ' (not_lt.mpr h)
  exact
    ((neumannSum_le_geometric_of_margin A b hfiniteA ρ hρ0 hmargin i).trans_lt
      (ENNReal.mul_ne_top (ENNReal.inv_ne_top.mpr hsub) hb).lt_top).ne

/-!
## Unit S4b — (1−A)·neumannSum = b over ℝ≥0 (the finite regime)

**PROVENANCE (unit S4b; BP_IV §2 S-table row S4b + §1.5 S4 block).**

* Blueprint statement (§1.5 S4 block, VERBATIM): the `matrixToReal` /
  `vectorToReal` defs and the parent theorem `neumann_eq_solve_of_margin`.
* S-table row S4b: "(1−A)·neumannSum = b over ℝ≥0 (finite regime) |
  telescope on partial sums; pass to limit by S4a | dep S4a | MED |
  M04 Lemma 3.3".
* Math source of record: M04 Lemma 3.3 (finite-regime solve agreement).
* Proof route (same identity, with the telescoped limit packaged as a
  one-step contraction): S4a's finiteness (`neumannSum_ne_top_of_margin`)
  makes `toReal` of S1a's solution equation lawful, so the real vector
  `vectorToReal (neumannSum A b)` solves the REAL affine recursion — the
  row's "(1−A)·neumannSum = b" reading (`toReal_neumannSum_solves`).  The
  difference of two real solutions is a fixed point of `matrixToReal A`,
  and the strict row-sum margin kills every fixed point at a coordinate
  maximizing `|d ·|` (`fixedPoint_eq_zero_of_margin` — the sup-norm
  contraction that the telescope's remainder-term limit computes).
-/

/-- S4 def (BP_IV §1.5 VERBATIM): the entrywise `toReal` of the kernel
    matrix. -/
noncomputable def matrixToReal {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) : Matrix (Fin m) (Fin m) ℝ :=
  fun i j => (A i j).toReal

/-- S4 def (BP_IV §1.5 VERBATIM): the entrywise `toReal` of the entrance
    vector. -/
noncomputable def vectorToReal {m : ℕ}
    (b : Fin m → ℝ≥0∞) : Fin m → ℝ := fun i => (b i).toReal

/-- S4b step 1 (the row's "(1−A)·neumannSum = b over ℝ" identity, solved
    form): `toReal` of S1a's solution equation `S = b + A·S`.  S4a's
    finiteness clause makes every `toReal` split (sum, Finset sum, product)
    lawful. -/
theorem toReal_neumannSum_solves {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤) (hfiniteb : ∀ i, b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ) :
    vectorToReal (neumannSum A b)
      = vectorToReal b
        + (matrixToReal A).mulVec (vectorToReal (neumannSum A b)) := by
  funext i
  have hS : ∀ j, neumannSum A b j ≠ ⊤ :=
    neumannSum_ne_top_of_margin A b hfiniteA hfiniteb ρ hρ0 hρ1 hmargin
  have hrec : neumannSum A b i = b i + A.mulVec (neumannSum A b) i :=
    congrFun (neumannSum_solves A b) i
  have hmul_ne : A.mulVec (neumannSum A b) i ≠ ⊤ := by
    simp only [Matrix.mulVec, dotProduct]
    exact (ENNReal.sum_lt_top.mpr fun j _ =>
      (ENNReal.mul_ne_top (hfiniteA i j) (hS j)).lt_top).ne
  calc (neumannSum A b i).toReal
      = (b i + A.mulVec (neumannSum A b) i).toReal := by rw [← hrec]
    _ = (b i).toReal + (A.mulVec (neumannSum A b) i).toReal :=
        ENNReal.toReal_add (hfiniteb i) hmul_ne
    _ = (b i).toReal + ∑ j, (A i j).toReal * (neumannSum A b j).toReal := by
        simp only [Matrix.mulVec, dotProduct]
        rw [ENNReal.toReal_sum fun j _ =>
          ENNReal.mul_ne_top (hfiniteA i j) (hS j)]
        simp_rw [ENNReal.toReal_mul]
    _ = (vectorToReal b
          + (matrixToReal A).mulVec (vectorToReal (neumannSum A b))) i := rfl

/-- S4b step 2 (the "pass to limit" leg of the row sketch, packaged as a
    sup-norm contraction): under the strict row-sum margin, the only real
    fixed point of the kernel is 0 — evaluate at a coordinate maximizing
    `|d ·|` and price its row by the margin. -/
theorem fixedPoint_eq_zero_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (ρ : ℝ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ)
    (d : Fin m → ℝ) (hd : d = (matrixToReal A).mulVec d) :
    ∀ i, d i = 0 := by
  intro i
  obtain ⟨i₀, -, hmax⟩ :=
    Finset.exists_max_image Finset.univ (fun j => |d j|)
      ⟨i, Finset.mem_univ i⟩
  have hd₀ : d i₀ = ∑ j, (A i₀ j).toReal * d j := congrFun hd i₀
  have hbound : |d i₀| ≤ ρ * |d i₀| := by
    calc |d i₀| = |∑ j, (A i₀ j).toReal * d j| := by rw [← hd₀]
      _ ≤ ∑ j, |(A i₀ j).toReal * d j| := Finset.abs_sum_le_sum_abs _ _
      _ = ∑ j, (A i₀ j).toReal * |d j| := by
          simp_rw [abs_mul, abs_of_nonneg ENNReal.toReal_nonneg]
      _ ≤ ∑ j, (A i₀ j).toReal * |d i₀| :=
          Finset.sum_le_sum fun j _ =>
            mul_le_mul_of_nonneg_left (hmax j (Finset.mem_univ j))
              ENNReal.toReal_nonneg
      _ = (∑ j, (A i₀ j).toReal) * |d i₀| := (Finset.sum_mul ..).symm
      _ ≤ ρ * |d i₀| :=
          mul_le_mul_of_nonneg_right (hmargin i₀) (abs_nonneg _)
  have hzero : |d i₀| ≤ 0 := by
    by_contra h
    rw [not_le] at h
    exact absurd (hbound.trans_lt (mul_lt_of_lt_one_left h hρ1))
      (lt_irrefl _)
  exact abs_nonpos_iff.mp ((hmax i (Finset.mem_univ i)).trans hzero)

/-- **S4b** (M04 Lemma 3.3, finite-regime solve agreement; BP_IV §2 S-table
    row S4b; parent statement §1.5 VERBATIM): under the strict row-sum
    margin, `toReal` of the Neumann sum agrees with EVERY real solution of
    the affine recursion x = b + A·x.  Proof: step 1 exhibits
    `vectorToReal (neumannSum A b)` as one such solution; the difference
    from `x` is a fixed point of `matrixToReal A`, killed by step 2. -/
theorem neumann_eq_solve_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤) (hfiniteb : ∀ i, b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ)
    (x : Fin m → ℝ)
    (hx : x = vectorToReal b + (matrixToReal A).mulVec x) :
    ∀ i, (neumannSum A b i).toReal = x i := by
  intro i
  have hS := toReal_neumannSum_solves A b hfiniteA hfiniteb ρ hρ0 hρ1 hmargin
  have hd : vectorToReal (neumannSum A b) - x
      = (matrixToReal A).mulVec (vectorToReal (neumannSum A b) - x) := by
    calc vectorToReal (neumannSum A b) - x
        = (vectorToReal b
            + (matrixToReal A).mulVec (vectorToReal (neumannSum A b)))
          - (vectorToReal b + (matrixToReal A).mulVec x) := by
          rw [← hS, ← hx]
      _ = (matrixToReal A).mulVec (vectorToReal (neumannSum A b))
          - (matrixToReal A).mulVec x := by abel
      _ = (matrixToReal A).mulVec (vectorToReal (neumannSum A b) - x) :=
          (Matrix.mulVec_sub _ _ _).symm
  have h0 : vectorToReal (neumannSum A b) i - x i = 0 :=
    fixedPoint_eq_zero_of_margin A ρ hρ1 hmargin _ hd i
  exact sub_eq_zero.mp h0

/-!
## Unit S2b — `seriesSum_eq_lfp`: the K1 recursion forces seriesSum = the lfp

**PROVENANCE (unit S2b; BP_IV §2 S-table row S2b + §1.5 S2 block).**

* Blueprint statement (§1.5 S2 block): the theorem `seriesSum_eq_lfp`,
  transcribed byte-identically below.  S-table row S2b: "combine S0, S2a,
  and monotone convergence | deps S0,S1b,S2a | MED | M04 Thm 1 + Thm 4 K1
  leg".  Math source of record: M04 Lemma 3.1 half 2 (tree side) / Thm 4
  K1 leg.
* Dependency transcription (S2a NOT yet landed at S2b landing time; same
  discipline as the S3a section's `neumannSum` note): the `TreeRecursion`
  carrier and the S2a slice identity (`slice_eq_partialNeumann`) are
  transcribed here as S2b's dependencies.  If unit S2a lands its own copy,
  dedup keeps exactly this text.
* **DEVIATION RECORD (carrier only; flagged for division-lead sign-off).**
  §1.5 displays `structure TreeRecursion … : Prop where stateOf : …`.
  Lean 4.31 REJECTS that ascription — a `Prop`-valued structure cannot
  carry data fields; the exact error is: "failed to generate projection
  `TreeRecursion.stateOf` for the 'Prop'-valued type `TreeRecursion`,
  field must be a proof, but it has type\n  SplittingType n → Fin m" —
  and without the projection the §1.5-displayed THEOREM (`hrec.stateOf σ`)
  cannot even be stated.  The single deviation below drops the `: Prop`
  ascription (the structure lands in `Type`); every field is byte-
  identical, and the S2b THEOREM statement is byte-identical to §1.5.
  No weakening: the same fields are packaged, and the blueprint's own
  display of `hrec.stateOf` presupposes working projections.
* Proof route (the row sketch): `series_eq_iSup` reads seriesSum as
  ⨆ N (slice at the σ state); S2a rewrites slice N as the partial Neumann
  sum over `range (N+1)`; monotone convergence in ℝ≥0∞
  (`ENNReal.tsum_eq_iSup_nat'` along the cofinal reindexing N ↦ N+1)
  closes against `neumannSum`'s tsum.
-/

open MovesU (ClassifierSpec FiberSeries SplittingType) in
/-- S2 carrier (M04 Lemma 3.1 half 2, the tree side; BP_IV §1.5 — fields
    VERBATIM, `: Prop` ascription dropped per the section's deviation
    record): the hypothesis structure whose fields are EXACTLY what K1
    supplies — per-σ, the level-N slice sum = entrance row + kernel
    matrix · level-(N−1) slice sums. -/
structure TreeRecursion {n p m : ℕ} [Fact p.Prime]
    (X : ClassifierSpec n p) (F : FiberSeries n p X)
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞) where
  stateOf : SplittingType n → Fin m
  slice : ℕ → Fin m → ℝ≥0∞
  slice_zero : slice 0 = b
  slice_succ : ∀ N, slice (N + 1) = b + A.mulVec (slice N)
  series_eq_iSup : ∀ σ, F.seriesSum σ = ⨆ N, slice N (stateOf σ)

/-- S2a helper (the partial-sum reorganization, standalone form of the
    `hstep` identity inside `partialNeumann_le_solution`): the range-(N+1)
    partial Neumann sum = entrance row + kernel · range-N partial sum. -/
theorem partialNeumann_succ {m : ℕ} (A : Matrix (Fin m) (Fin m) ℝ≥0∞)
    (b : Fin m → ℝ≥0∞) (N : ℕ) :
    ∑ k ∈ Finset.range (N + 1), (A ^ k).mulVec b
      = b + A.mulVec (∑ k ∈ Finset.range N, (A ^ k).mulVec b) := by
  rw [Finset.sum_range_succ', Matrix.mulVec_sum]
  simp only [pow_succ', pow_zero, Matrix.one_mulVec, ← Matrix.mulVec_mulVec]
  exact add_comm _ b

/-- **S2a content** (transcribed dependency; BP_IV §2 S-table row S2a:
    "recursion identifies every finite slice with a partial Neumann sum |
    induction on N using `TreeRecursion.slice_zero/slice_succ`"): any slice
    family satisfying the K1 recursion equals the partial Neumann sums.
    Stated over bare `slice_zero`/`slice_succ` laws so the structure
    packaging is orthogonal. -/
theorem slice_eq_partialNeumann {m : ℕ} {A : Matrix (Fin m) (Fin m) ℝ≥0∞}
    {b : Fin m → ℝ≥0∞} {slice : ℕ → Fin m → ℝ≥0∞}
    (h0 : slice 0 = b) (hs : ∀ N, slice (N + 1) = b + A.mulVec (slice N)) :
    ∀ N, slice N = ∑ k ∈ Finset.range (N + 1), (A ^ k).mulVec b := by
  intro N
  induction N with
  | zero => simp [h0, Matrix.one_mulVec]
  | succ N ih => rw [hs N, ih, ← partialNeumann_succ]

open MovesU (ClassifierSpec FiberSeries SplittingType) in
/-- **S2b** (M04 Thm 1 + Thm 4 K1 leg; BP_IV §1.5 VERBATIM, §2 S-table row
    S2b): any `FiberSeries` whose slice sums satisfy the K1 recursion has
    seriesSum = the least fixed point (the Neumann sum) at its state.
    Proof per the row sketch: `series_eq_iSup` + the S2a slice identity +
    monotone convergence (`ENNReal.tsum_eq_iSup_nat'` along N ↦ N+1). -/
theorem seriesSum_eq_lfp {n p m : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    (hrec : TreeRecursion X F A b) :
    ∀ σ : SplittingType n,
      F.seriesSum σ = neumannSum A b (hrec.stateOf σ) := by
  intro σ
  have hslice := slice_eq_partialNeumann hrec.slice_zero hrec.slice_succ
  calc F.seriesSum σ
      = ⨆ N, hrec.slice N (hrec.stateOf σ) := hrec.series_eq_iSup σ
    _ = ⨆ N, ∑ k ∈ Finset.range (N + 1), (A ^ k).mulVec b (hrec.stateOf σ) := by
        refine iSup_congr fun N => ?_
        rw [hslice N]
        simp [Finset.sum_apply]
    _ = ∑' k, (A ^ k).mulVec b (hrec.stateOf σ) :=
        (ENNReal.tsum_eq_iSup_nat' (Filter.tendsto_add_atTop_nat 1)).symm
    _ = neumannSum A b (hrec.stateOf σ) := rfl

/-!
## Unit S4c1 — finite evaluation: the Neumann value IS the Cramer/matrix solve

**PROVENANCE (unit S4c1; BP_IV §2 S-table row S4c, finite-evaluation leg;
§4 wave split S4a → S4b → S4c1 → S4c2; §1.5 S4 block).**

* Parent statement (§1.5 S4 block, VERBATIM): `neumann_eq_solve_of_margin`
  — already landed above with the `matrixToReal`/`vectorToReal` defs (S4b
  section); S4c1 transcribes nothing anew and changes NO signature.
* S-table row S4c, the leg landed here: "Cramer: (1−K_e(q₀)) invertible by
  M4; solution unique (S1b + finiteness) = matrix solve".  The kernel's
  invertibility arrives as the EXPLICIT binder `hdet` (the nonzero-
  determinant shape M4's `r1_margin_of_regP` prices through
  `RegP.detFull_ne_zero`/`cycS_eval_pos` per §3's corpus-reuse map) — a
  named hypothesis, never an axiom, per the [M]-hypothesis discipline.
  The tie to `SolveSeam.r_is_solve`'s `Rsh` (engine vocabulary; the
  Cramer/adjugate route named in `DefsLedger`) is unit S4c2, NOT here.
* Math source of record: M04 Lemma 3.3 + O11 K2 (evaluation plumbing).
* Proof: the Cramer solve `x := (1 − A_ℝ)⁻¹ · b_ℝ` satisfies the real
  affine recursion — multiply through by `1 − A_ℝ`, lawful by `hdet` via
  `Matrix.mul_nonsing_inv` — so the parent uniqueness
  (`neumann_eq_solve_of_margin`) evaluates the Neumann sum at it.
-/

/-- **S4c1** (M04 Lemma 3.3 + O11 K2, the finite-evaluation leg of S-table
    row S4c; BP_IV §4 wave split): under the strict row-sum margin and a
    nonzero determinant of `1 − A_ℝ` (M4's output shape, carried as the
    explicit binder `hdet`), the real evaluation of the Neumann sum is
    EXACTLY the Cramer/matrix solve `(1 − A_ℝ)⁻¹ · b_ℝ`.  Binders are the
    parent `neumann_eq_solve_of_margin`'s (§1.5 VERBATIM display) with the
    abstract solution `(x, hx)` replaced by the determinant hypothesis that
    constructs it. -/
theorem neumann_eq_matrixSolve_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤) (hfiniteb : ∀ i, b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ)
    (hdet : (1 - matrixToReal A).det ≠ 0) :
    ∀ i, (neumannSum A b i).toReal
      = (1 - matrixToReal A)⁻¹.mulVec (vectorToReal b) i := by
  set M := matrixToReal A with hM
  set c := vectorToReal b with hc
  set x := (1 - M)⁻¹.mulVec c with hxdef
  have hunit : IsUnit (1 - M).det := isUnit_iff_ne_zero.mpr hdet
  have hsolve : (1 - M).mulVec x = c := by
    rw [hxdef, Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hunit,
      Matrix.one_mulVec]
  have hx : x = c + M.mulVec x := by
    have h1 : x - M.mulVec x = c := by
      rw [← hsolve, Matrix.sub_mulVec, Matrix.one_mulVec]
    rw [← h1]
    abel
  exact neumann_eq_solve_of_margin A b hfiniteA hfiniteb ρ hρ0 hρ1 hmargin x hx

/-!
## Unit S5b — the original obstruction record (superseded at REVISION 3;
## the landed adjudicated form is at the END of this file)

**REVISION-3 disposition:** the two obstructions below were adjudicated by the
mop-up architect (full record: `blueprints/BP_IV.md` REVISION 3 + the S5b
section at the end of this file): (i) the five undeclared row types become
OPAQUE PREDICATE PARAMETERS (`K3DeltaRow` pattern, per the H4 ledger in
`ValueSide/Hyps.lean`) resp. the landed `CensusValueRows` form of
`Census.lean`; (ii) the display's missing (A, b) ↔ chain link becomes the ONE
new named row `SolvePricing` (the O11-K2 pricing content the S4c2/S5a units
already expose).  The original record is kept verbatim below — it is the
type-level half of the warrant.

**BLOCKED(S5b)** (checked at compile, 2026-08-01; probe = the §1.5-VERBATIM
statement with a `sorry` body over the full value-side import set
`SeriesTie + ValueSide.Hyps + ValueSide.Census + DictIII.Hyps`).  The Step-18
capstone's binder list cannot elaborate: FIVE of its row types are declared
NOWHERE in the corpus, each an "unknown identifier" hard error (not a
`sorry`-able goal), e.g. verbatim: "error: Function expected at\n  GRBRow\n
but this term has type\n  ?m.1 … The identifier `GRBRow` is unknown".
Per BP_IV §1.0 ("if an owner has not landed, that consuming unit is blocked
rather than compiled against a weaker signature") no local alias is declared:
 · `GRBRow CD` / `FreshRow CD` — owner BP_III (GD dictionary).  NOTE the
   landed `DictIII.GRB p F` / `DictIII.FRESH p F` rows carry a DIFFERENT
   signature (prime + finite field, not `CensusData`) — the §1.5 binder needs
   the CensusData-indexed form, which does not exist.
 · `CensusValueRows CD` — BP_IV's own C5 row (Census.lean header: "Later
   waves add … C5/C5′"); its §1.2 display also references the undeclared
   `StratumR`/`JunctionStratum` carriers and the BP_III `GRBRow`/`FreshRow`,
   and the §3 E-phase note re-keys it over the SlotsG15 `SiteData` carriers
   — so the C5-row statement itself is blocked on the BP_III owner modules.
 · `R1R4Row n p X` — owner BP_V (`Scaffold/RowStatements.lean`): absent
   (Hyps.lean H4 ledger: "Consumer blocked: S5 (K3-c leg)").
 · `TerminalSeamRows n p X F` — owner BP_III (CU-2t; `DictIII/CU2t.lean`):
   absent (H4 ledger: "Consumer blocked: S5 (K4/D-a leg)").
Everything ELSE in the §1.5 statement elaborates (probe-verified): all other
binder types (`UCarriers`/`ClassifierSpec`/`FiberSeries`/`CensusData`/
`RegData`/`AssembledPack`/`PackReference`/`TreeSeam`/`TreeRecursion`/`RegP`/
`RegPin`/`PackCorrespondence`/`ADMFull`/`K3DeltaRow`) and the conclusion row
`F.seriesSum σ = ENNReal.ofReal (C.chain.Rval (vmap C.T σ) (p : ℚ))`
(byte-matching `BridgeKernels.series_tie`).  Also outstanding at S5b time:
proof-deps S5a (state/block reindexing), S3b2, S4c2 not yet landed.  M04 F1
fence stands: the DEVICE `n2Chain` must never instantiate S5's carriers.
-/

/-!
## Unit S5a — state/block reindexing: the first split of the S5 assembly

**PROVENANCE (unit S5a; BP_IV §4 wave 3 "S5a (state/block reindexing) →
S5b (`seriesTie_of_kernels`) → D4"; parent statement §1.5 S5 + §2 S-table
row S5).**

* HONESTY NOTE (statement provenance): BP_IV displays NO standalone S5a
  Lean statement — §2's closing note splits the composite S5 row at
  assignment time ("each assignment targeting one definition or one proof
  idea").  The §1.5-VERBATIM parent `seriesTie_of_kernels` is owned by
  unit S5b (BLOCKED above, owner rows absent) and is NOT touched here; no
  displayed signature is changed.  Per this file's standing split-unit
  discipline (S3b1's and S4a's helper layers), S5a lands the named glue
  the parent's proof route consumes.
* The proof idea (M04 Thm 4 assembly, the reindexing leg; O11 r3 §tiers):
  the per-σ series value is read AT THE σ-STATE (`hrec.stateOf σ`, S2b's
  K1 leg), that state lives in the active BLOCK PREFIX (`i.1 < k`, the
  Bekić passage of M04 Lemma 3.2 — S3a's truncation), and the truncated
  Neumann value crosses to ℝ and back through the margin evaluation
  (S4a's finiteness + S4b's uniqueness + S4c1's Cramer solve).  S5a
  packages exactly this composite, so S5b's remaining content is purely
  the row identifications (K3 census + K4 seam + S4c2's `Rsh` tie).
* Deps at landing time: S2b (`seriesSum_eq_lfp`), S3a
  (`neumannSum_blockTriangular`), S4a (`neumannSum_ne_top_of_margin`),
  S4b (`neumann_eq_solve_of_margin`), S4c1
  (`neumann_eq_matrixSolve_of_margin`) — all landed above.  S3b2 and
  S4c2 had NOT landed at S5a landing time; they are S5b-side inputs
  (chained truncation resp. `SolveSeam` agreement), consumed there, not
  here.
* The prefix-transport lemmas exist so S5b may price the truncated system
  from FULL-system finiteness/margin rows when that is the form M3'/M4
  deliver.
-/

/-- S5a transport (block reindexing bookkeeping): entrywise finiteness
    descends from the kernel to its prefix truncation. -/
theorem prefixMatrix_ne_top {m k : ℕ} {A : Matrix (Fin m) (Fin m) ℝ≥0∞}
    (hfiniteA : ∀ i j, A i j ≠ ⊤) :
    ∀ i j, prefixMatrix k A i j ≠ ⊤ := by
  intro i j
  show (if i.1 < k ∧ j.1 < k then A i j else 0) ≠ ⊤
  split_ifs with h
  · exact hfiniteA i j
  · exact ENNReal.zero_ne_top

/-- S5a transport: entrywise finiteness descends from the entrance vector
    to its prefix truncation. -/
theorem prefixVector_ne_top {m k : ℕ} {b : Fin m → ℝ≥0∞}
    (hfiniteb : ∀ i, b i ≠ ⊤) :
    ∀ i, prefixVector k b i ≠ ⊤ := by
  intro i
  show (if i.1 < k then b i else 0) ≠ ⊤
  split_ifs with h
  · exact hfiniteb i
  · exact ENNReal.zero_ne_top

/-- S5a transport: the row-sum margin descends from the kernel to its
    prefix truncation (each truncated entry is the original or 0). -/
theorem prefixMatrix_rowSum_toReal_le {m k : ℕ}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {ρ : ℝ}
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ) :
    ∀ i, ∑ j, (prefixMatrix k A i j).toReal ≤ ρ := by
  intro i
  refine le_trans (Finset.sum_le_sum fun j _ => ?_) (hmargin i)
  show (if i.1 < k ∧ j.1 < k then A i j else 0).toReal ≤ (A i j).toReal
  split_ifs with h
  · exact le_rfl
  · simp

/-- S5a core (the ofReal/toReal reindexing of the margin evaluation):
    under S4b's exact binders (§1.5 VERBATIM display), the ℝ≥0∞ Neumann
    value IS `ofReal` of the real affine solution — S4a's finiteness makes
    the round trip lawful. -/
theorem neumannSum_eq_ofReal_solve_of_margin {m : ℕ}
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤) (hfiniteb : ∀ i, b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ)
    (x : Fin m → ℝ)
    (hx : x = vectorToReal b + (matrixToReal A).mulVec x) :
    ∀ i, neumannSum A b i = ENNReal.ofReal (x i) := by
  intro i
  rw [← neumann_eq_solve_of_margin A b hfiniteA hfiniteb ρ hρ0 hρ1 hmargin x hx i]
  exact (ENNReal.ofReal_toReal
    (neumannSum_ne_top_of_margin A b hfiniteA hfiniteb ρ hρ0 hρ1 hmargin i)).symm

open MovesU (ClassifierSpec FiberSeries SplittingType) in
/-- **S5a, state leg** (σ ↦ state reindexing): a K1 recursion (S2b) plus
    the margin evaluation reads the per-σ series value off the real
    solution vector AT THE σ-STATE. -/
theorem seriesSum_eq_ofReal_solve {n p m : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    (hrec : TreeRecursion X F A b)
    (hfiniteA : ∀ i j, A i j ≠ ⊤) (hfiniteb : ∀ i, b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ)
    (x : Fin m → ℝ)
    (hx : x = vectorToReal b + (matrixToReal A).mulVec x) :
    ∀ σ : SplittingType n,
      F.seriesSum σ = ENNReal.ofReal (x (hrec.stateOf σ)) := fun σ =>
  (seriesSum_eq_lfp hrec σ).trans
    (neumannSum_eq_ofReal_solve_of_margin A b hfiniteA hfiniteb ρ hρ0 hρ1
      hmargin x hx (hrec.stateOf σ))

open MovesU (ClassifierSpec FiberSeries SplittingType) in
/-- **S5a, block leg** (state/block reindexing — THE unit deliverable):
    when every σ-state lives in the block prefix `i.1 < k` of a
    block-triangular kernel, the per-σ series value is `ofReal` of the
    TRUNCATED system's real solution at the σ-state — the M04 Lemma 3.2
    Bekić passage threaded through S2b + S3a + S4a/S4b.  The margin and
    finiteness binders are those of the truncated system (descend from the
    full system via the transport lemmas above when needed). -/
theorem seriesSum_eq_ofReal_prefixSolve {n p m : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    (hrec : TreeRecursion X F A b) (k : ℕ)
    (htri : ∀ i j, i.1 < k → k ≤ j.1 → A i j = 0)
    (hstate : ∀ σ : SplittingType n, (hrec.stateOf σ).1 < k)
    (hfiniteA : ∀ i j, prefixMatrix k A i j ≠ ⊤)
    (hfiniteb : ∀ i, prefixVector k b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (prefixMatrix k A i j).toReal ≤ ρ)
    (x : Fin m → ℝ)
    (hx : x = vectorToReal (prefixVector k b)
      + (matrixToReal (prefixMatrix k A)).mulVec x) :
    ∀ σ : SplittingType n,
      F.seriesSum σ = ENNReal.ofReal (x (hrec.stateOf σ)) := by
  intro σ
  rw [seriesSum_eq_lfp hrec σ,
    neumannSum_blockTriangular A b htri (hrec.stateOf σ) (hstate σ)]
  exact neumannSum_eq_ofReal_solve_of_margin _ _ hfiniteA hfiniteb ρ hρ0 hρ1
    hmargin x hx (hrec.stateOf σ)

open MovesU (ClassifierSpec FiberSeries SplittingType) in
/-- **S5a, solved block leg** (the composite with S4c1's Cramer form —
    the exact shape S5b rewrites by the K3/K4 rows and S4c2's `Rsh` tie):
    with a nonzero determinant on the truncated system (M4's output
    shape), the per-σ series value is `ofReal` of the truncated matrix
    solve at the σ-state. -/
theorem seriesSum_eq_ofReal_prefixMatrixSolve {n p m : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    (hrec : TreeRecursion X F A b) (k : ℕ)
    (htri : ∀ i j, i.1 < k → k ≤ j.1 → A i j = 0)
    (hstate : ∀ σ : SplittingType n, (hrec.stateOf σ).1 < k)
    (hfiniteA : ∀ i j, prefixMatrix k A i j ≠ ⊤)
    (hfiniteb : ∀ i, prefixVector k b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (prefixMatrix k A i j).toReal ≤ ρ)
    (hdet : (1 - matrixToReal (prefixMatrix k A)).det ≠ 0) :
    ∀ σ : SplittingType n,
      F.seriesSum σ = ENNReal.ofReal
        ((1 - matrixToReal (prefixMatrix k A))⁻¹.mulVec
          (vectorToReal (prefixVector k b)) (hrec.stateOf σ)) := by
  intro σ
  rw [seriesSum_eq_lfp hrec σ,
    neumannSum_blockTriangular A b htri (hrec.stateOf σ) (hstate σ),
    ← neumann_eq_matrixSolve_of_margin _ _ hfiniteA hfiniteb ρ hρ0 hρ1
      hmargin hdet (hrec.stateOf σ)]
  exact (ENNReal.ofReal_toReal
    (neumannSum_ne_top_of_margin _ _ hfiniteA hfiniteb ρ hρ0 hρ1 hmargin
      (hrec.stateOf σ))).symm

/-!
## Unit S4c2 — the SolveSeam agreement: the `r_is_solve`/`Rsh` tie under RegP

**PROVENANCE (unit S4c2; BP_IV §2 S-table row S4c, SolveSeam-agreement leg;
§4 wave split S4a → S4b → S4c1 → S4c2; §3 corpus-reuse map rows
"`SolveSeam` (+ `r_is_solve`, `R_defined`) (`DefsLedger.lean:578`) | the
solve pin to `MovesS.Rsh` | S4c, S5 (K2 leg)" and
"`RegP.detFull_ne_zero` … | M4, S4c".)**

* HONESTY NOTE (statement provenance; same discipline as the S5a section):
  BP_IV displays NO standalone S4c2 Lean statement — §2's closing note
  splits the composite S4c row at assignment time.  The §1.5-VERBATIM S4
  parent `neumann_eq_solve_of_margin` is landed (S4b) and untouched; NO
  displayed signature is changed here.  S4c2 lands exactly the S-table
  row's remaining leg: "agreement with the RatFunc solve value at q₀ under
  RegP … tie to `SolveSeam.r_is_solve`'s `Rsh`".
* THE TIE, in the corpus's own vocabulary (all BY IMPORT, §3 discipline):
  the solve pin arrives as the EXPLICIT binder `hsolve`, byte-identical in
  type to the corpus field `SolveSeam.r_is_solve` (`DefsLedger.lean:578`)
  — the pin of the abstract solve output `S.R σ` to THE real Cramer/
  adjugate solve `MovesS.Rsh` over the blockSolve.  It is a named
  hypothesis row, NEVER the full `SolveSeam` (whose OTHER field is
  `series_tie`, the [3t] TARGET row — binding the full seam here would be
  circular for S5b).  Under (REG-p) — `hreg : RegP D` through
  `hpin : RegPin C D`, M4's evaluation regime — `RegPin.detHyp` supplies
  `DetHyp`, and the chain's OWN solve law `rsh_interp` (RS.4) evaluates
  that `Rsh` at q₀ = p to the measured value `Rval`: so the literal
  evaluation `evalℝ S σ p` of the pinned solve IS
  `C.chain.Rval (vmap C.T σ) (p : ℚ)` (`evalℝ_eq_Rval_of_solvePin` —
  the standalone-leg form of the corpus `SolveSeam.evalℝ_eq_Rval`
  derivation, NOT an alias: it consumes the leg, not the seam).
* The unit theorem (`neumann_eq_solveValue_of_margin`) then ties S4's
  margin evaluation to that value: any real affine solution `x` read off
  at the σ-state by the evaluated solve (`hread`, the O11-K2 evaluation-
  plumbing row — a named binder for the identification S5b's K3/K4 census
  rows will discharge) prices the Neumann value AT q₀: it equals the
  RatFunc solve value `evalℝ S σ p` AND the chain's measured
  `Rval (vmap C.T σ) (p : ℚ)`.
* Math source of record: M04 Lemma 3.3 + O11 K2.
* Deps: S4b (`neumann_eq_solve_of_margin`, landed), S4c1 (landed;
  its Cramer form is the canonical `x` supplier), M4's row shape
  (`r1_margin_of_regP`; consumed as the (REG-p) binders, per §3).
-/

/-- S4c2 pin tie (the `Rsh` leg of S-table row S4c; the standalone-leg form
    of the corpus `SolveSeam.evalℝ_eq_Rval` derivation — consumes ONLY the
    `r_is_solve`-shaped pin `hsolve`, never the full `SolveSeam`, so S5b can
    use it without assuming the [3t] target row): under (REG-p), the literal
    evaluation of the pinned solve output at q₀ = p IS the chain's measured
    value — `S.R σ` is `Rsh` by the pin, and RS.4's own solve law
    `rsh_interp` evaluates `Rsh` to `Rval` at the prime pool. -/
theorem evalℝ_eq_Rval_of_solvePin {n p : ℕ} {C : MovesU.UCarriers n}
    {S : MovesU.SolveData n} {D : MovesU.RegData p}
    (hpin : MovesU.RegPin C D) (hreg : MovesU.RegP D) (hp : p.Prime)
    (hsolve : ∀ (hdet : MovesS.DetHyp C.T C.RB C.hK)
      (σ : MovesU.SplittingType n),
      S.R σ = MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP
        (MovesU.vmap C.T σ))
    (σ : MovesU.SplittingType n) :
    MovesU.evalℝ S σ p = C.chain.Rval (MovesU.vmap C.T σ) (p : ℚ) := by
  have hdet : MovesS.DetHyp C.T C.RB C.hK := hpin.detHyp hreg
  have hpP : ((p : ℚ)) ∈ C.chain.PrimePools :=
    (C.chain.prime_base _).mpr ⟨p, hp, rfl⟩
  obtain ⟨hok, heval⟩ :=
    C.chain.rsh_interp (MovesU.vmap C.T σ) (C.vmap_mem_Sigmas σ) (p : ℚ) hpP hdet
  have hkey : MovesU.evalℝ S σ p
      = ((MovesS.evalAt (p : ℚ)
          ⟨MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP
            (MovesU.vmap C.T σ), hok⟩ : ℚ) : ℝ) := by
    unfold MovesU.evalℝ
    rw [hsolve hdet σ]
    rfl
  rw [hkey]
  exact heval

/-- **S4c2** (M04 Lemma 3.3 + O11 K2; BP_IV §2 S-table row S4c, the
    SolveSeam-agreement leg): agreement with the RatFunc solve value at
    q₀ = p under RegP.  Any real affine solution `x` of the margin system
    that reads off the evaluated solve at the σ-state (`hread`) prices the
    Neumann value as BOTH the literal solve evaluation `evalℝ S σ p` (the
    solve output pinned to `MovesS.Rsh` by the `r_is_solve`-shaped binder
    `hsolve`) AND the chain's measured value `Rval` — the K2 leg S5b
    consumes. -/
theorem neumann_eq_solveValue_of_margin {n p m : ℕ} {C : MovesU.UCarriers n}
    {S : MovesU.SolveData n} {D : MovesU.RegData p}
    (hpin : MovesU.RegPin C D) (hreg : MovesU.RegP D) (hp : p.Prime)
    (hsolve : ∀ (hdet : MovesS.DetHyp C.T C.RB C.hK)
      (σ : MovesU.SplittingType n),
      S.R σ = MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP
        (MovesU.vmap C.T σ))
    (A : Matrix (Fin m) (Fin m) ℝ≥0∞) (b : Fin m → ℝ≥0∞)
    (hfiniteA : ∀ i j, A i j ≠ ⊤) (hfiniteb : ∀ i, b i ≠ ⊤)
    (ρ : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hmargin : ∀ i, ∑ j, (A i j).toReal ≤ ρ)
    (stateOf : MovesU.SplittingType n → Fin m)
    (x : Fin m → ℝ)
    (hx : x = vectorToReal b + (matrixToReal A).mulVec x)
    (hread : ∀ σ : MovesU.SplittingType n,
      x (stateOf σ) = MovesU.evalℝ S σ p) :
    ∀ σ : MovesU.SplittingType n,
      (neumannSum A b (stateOf σ)).toReal = MovesU.evalℝ S σ p
        ∧ (neumannSum A b (stateOf σ)).toReal
            = C.chain.Rval (MovesU.vmap C.T σ) (p : ℚ) := by
  intro σ
  have h1 : (neumannSum A b (stateOf σ)).toReal = MovesU.evalℝ S σ p :=
    (neumann_eq_solve_of_margin A b hfiniteA hfiniteb ρ hρ0 hρ1 hmargin x hx
      (stateOf σ)).trans (hread σ)
  exact ⟨h1, h1.trans (evalℝ_eq_Rval_of_solvePin hpin hreg hp hsolve σ)⟩

/-!
## Unit S5b — `seriesTie_of_kernels` (LANDED at REVISION 3, mop-up adjudication)

**REVISION-3 adjudication record (S5b; full blueprint record in
`blueprints/BP_IV.md` REVISION 3; the original compile-probe obstruction
record stands verbatim in the superseded S5b section above).**  Two repairs,
both intent-preserving against the landed reality:

1. **The five undeclared row types** (`GRBRow`/`FreshRow`/`CensusValueRows`/
   `R1R4Row`/`TerminalSeamRows` — the §1.5 display could not ELABORATE, so
   there is nothing compiled to refute; the probe error transcript above is
   the type-level warrant).  Per the H4 ledger ruling (`ValueSide/Hyps.lean`):
   (GR-B)/(FRESH) enter as the opaque parameters
   `{GRBRow FreshRow : CensusData → Prop}` (BP_III instantiates, no re-key);
   `CensusValueRows` is the landed C5 row of `Census.lean` (strata-parametric
   form, binders `SW`/`SJ`); (R1)–(R4) enters as
   `{R1R4Row : ClassifierSpec n p → Prop}` applied at `X` (display token
   `R1R4Row n p X` → parameter at `X`, its indices riding in the parameter's
   type); (H6) enters as `{TerminalSeamRows : FiberSeries n p X → Prop}`
   applied at `F` ("keyed at F", ibid.).

2. **The missing (A, b) ↔ chain link** (the proof-level warrant): in the
   §1.5 display NOTHING ties the abstract kernel pair (A, b) — or `F` — to
   `C.chain`'s solve values; the displayed conclusion mentions only `F` and
   `C`, while (A, b) range over ALL pairs admitting a `TreeRecursion` for
   `F`.  Under-constraint shape (the countermodel that would compile once
   heavyweight seam instances exist; not built — the display never
   elaborated, so no compiled witness is owed): take `A = 0`, `b = 0`, `F`
   with all slice sums 0 (then `TreeRecursion` holds with `slice ≡ 0`,
   forcing `F.seriesSum ≡ 0` through `series_eq_iSup`), every opaque row
   instantiated `fun _ => True`, and any carrier `C` with some
   `Rval (vmap C.T σ) p ≠ 0` — the conclusion fails.  The mathematics the
   display omitted is EXACTLY O-11 K2's evaluation plumbing (M04 Lemma 3.3's
   application scope): the kernel system's real solution reads off the
   chain's solve values at the σ-states.  That content is landed as the ONE
   new NAMED row `SolvePricing` below ([M]-hypothesis discipline: a named
   structure, never an axiom, never silently strengthened), whose fields are
   precisely the binders the landed S5a/S4c2 units expose — the census rows
   (K3) and seam rows (K4) are what will DISCHARGE a `SolvePricing` instance
   when BP_III's product-law instances land; here they ride as the honest
   conditionality display, exactly as §1.5 charges ("S5's binder list IS the
   honest conditionality display").

Proof = the S5a state leg (`seriesSum_eq_ofReal_solve`: S2b + S4a/S4b) chained
through the pricing row's read-off into the S4c2 pin tie
(`evalℝ_eq_Rval_of_solvePin`).  The M04 F1 fence stands: the DEVICE `n2Chain`
must never instantiate these carriers.
-/

open MovesU (ClassifierSpec FiberSeries SplittingType) in
/-- S5b pricing row (**REVISION 3**, the K2/K3-leg [M] hypothesis): the O11-K2
    evaluation-plumbing content tying the abstract kernel pair (A, b) to the
    carrier chain's solve values — a solve datum pinned to the real
    Cramer/adjugate `Rsh` (field `solve_pin`, byte-identical in type to the
    corpus `SolveSeam.r_is_solve`), the row-sum margin regime of M3'/M4
    (fields `finiteA/finiteb/ρ/margin`), and a real affine solution of the
    kernel system that reads off the evaluated solve at every σ-state
    (fields `sol/sol_solves/sol_reads`), nonnegatively (`sol_nonneg` — the
    O-12 positivity layer's shape, `cycS_eval_pos` at q₀ = p ≥ 2; consumed by
    D4's `toReal` passage).  Constructors are owner-side (BP_III product-law
    instances + the census value rows); no proof of this row exists at this
    campaign. -/
structure SolvePricing {n p m : ℕ} [Fact p.Prime]
    {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    (C : MovesU.UCarriers n) (K1 : TreeRecursion X F A b) where
  S : MovesU.SolveData n
  solve_pin : ∀ (hdet : MovesS.DetHyp C.T C.RB C.hK) (σ : SplittingType n),
    S.R σ = MovesS.Rsh C.T C.MS C.RB C.hdc C.hK hdet C.Fam C.chain.WshP
      (MovesU.vmap C.T σ)
  finiteA : ∀ i j, A i j ≠ ⊤
  finiteb : ∀ i, b i ≠ ⊤
  ρ : ℝ
  ρ_nonneg : 0 ≤ ρ
  ρ_lt_one : ρ < 1
  margin : ∀ i, ∑ j, (A i j).toReal ≤ ρ
  sol : Fin m → ℝ
  sol_solves : sol = vectorToReal b + (matrixToReal A).mulVec sol
  sol_reads : ∀ σ : SplittingType n, sol (K1.stateOf σ) = MovesU.evalℝ S σ p
  sol_nonneg : ∀ σ : SplittingType n, 0 ≤ sol (K1.stateOf σ)

-- The row binders of the honest-conditionality display are deliberately
-- unused in the Lean assembly (their content is consumed at instance-
-- construction time, not here); the lint is silenced for S5b only, the D3
-- precedent (`DensityTie.lean`).
set_option linter.unusedVariables false in
open MovesU (ClassifierSpec FiberSeries SplittingType) in
open ValueSide in
/-- **S5b** (`seriesTie_of_kernels`, THE movement's Step-18 capstone; BP_IV
    §1.5 at the REVISION-3 adjudicated scope — see the adjudication record
    above): `series_tie` from the displayed row list, one binder per ROOT
    consumption — K1 = `hrec`-shaped recursion (BP_III's SibJcRows feed it),
    K2 = `hreg`/`hpin`/`K2 : SolvePricing` (+ `hpack`), K3 = the census
    binders (`hGRB`, `hFresh`, `hadm`, `hcen`, `hR14`, `hK3δ`), K4 = the
    terminal-seam row + the `TreeSeam` in scope.  Conclusion: the corpus row
    `BridgeKernels.series_tie`, verbatim.  The BP_VI spine must consume this
    binder list VERBATIM (§5 statement fence). -/
theorem seriesTie_of_kernels {n p m : ℕ} [Fact p.Prime]
    {C : MovesU.UCarriers n} {X : ClassifierSpec n p} {F : FiberSeries n p X}
    {CD : CensusData} {RD : MovesU.RegData p} {P : AssembledPack n}
    {R : PackReference n C P}
    {A : Matrix (Fin m) (Fin m) ℝ≥0∞} {b : Fin m → ℝ≥0∞}
    {GRBRow FreshRow : CensusData → Prop}
    {SW : StratumR CD} {SJ : JunctionStratum CD}
    {R1R4Row : ClassifierSpec n p → Prop}
    {TerminalSeamRows : FiberSeries n p X → Prop}
    {RealizedPool DeltaStablePos : ℕ → Prop}
    (seam : MovesU.TreeSeam n p X F)
    (K1 : TreeRecursion X F A b)
    (hreg : MovesU.RegP RD) (hpin : MovesU.RegPin C RD)
    (K2 : SolvePricing C K1)
    (hpack : PackCorrespondence n C P R)
    (hGRB : GRBRow CD) (hFresh : FreshRow CD) (hadm : ADMFull CD)
    (hcen : CensusValueRows CD GRBRow FreshRow SW SJ)
    (hR14 : R1R4Row X)
    (hK3δ : K3DeltaRow p RD RealizedPool DeltaStablePos)
    (K4 : TerminalSeamRows F) :
    ∀ σ : SplittingType n,
      F.seriesSum σ
        = ENNReal.ofReal (C.chain.Rval (MovesU.vmap C.T σ) (p : ℚ)) := by
  intro σ
  have hp : p.Prime := Fact.out
  have h1 : F.seriesSum σ = ENNReal.ofReal (K2.sol (K1.stateOf σ)) :=
    seriesSum_eq_ofReal_solve K1 K2.finiteA K2.finiteb K2.ρ K2.ρ_nonneg
      K2.ρ_lt_one K2.margin K2.sol K2.sol_solves σ
  rw [h1, K2.sol_reads σ,
    evalℝ_eq_Rval_of_solvePin hpin hreg hp K2.solve_pin σ]

end LeanUrat.Scaffold
