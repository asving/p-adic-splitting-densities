/-
BP_IV §1.5 — Step 18, the resummation core + the tie assembly
(`SeriesTie.lean`).
Units in this file: SKEL (module skeleton) · S0 (seriesSum = ⨆ of slice sums —
located HERE so this file never depends on `DensityTie.lean`; REV-2 finding 5)
· S3a (Bekić block, with the §1.5-verbatim `neumannSum` def) · S1b (leastness)
· S1a (solution half + `neumannSum_isLFP`) · S4a (summability from the
row-sum margin — the power bound, geometric comparison, and finiteness).
Later waves add S2a/S2b (`seriesSum_eq_lfp`), S3b, S4b/S4c (telescope/solve
agreement, assembling the §1.5-verbatim parent `neumann_eq_solve_of_margin`),
and S5 (`seriesTie_of_kernels`, targeting the corpus row
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

end LeanUrat.Scaffold
