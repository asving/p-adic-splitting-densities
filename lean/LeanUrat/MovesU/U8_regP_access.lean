/-
Unit U8.regP_access  (MovesU campaign)  [definitional]
moves_ref: "(r1) det(I − K_e(q₀)) ≠ 0; and (r2) for EVERY member of the DISPLAYED
           ENTRY LIST E(e) := { each entry of K_e } ∪ { each entry of b_e — BOTH
           components … per-cell J … } ∪ { each entry of ι_e } ∪ { each W_Ŝ
           coefficient } ∪ { each entry of every β_{e,τ} … }" (SQ.4's rev-3 schema,
           covered in full)
deps: Defs.
sketch: unfold `RegP` + `RegData.entryList` (Finset union membership per family).
        The API the MovesS instantiation consumes; no content beyond the schema.
        `betaLeg_agree`'s per-pool coverage is provable BECAUSE `entryList` unions
        over `depthSet` (ruling (C)). `Wcoef_agree` needs no block argument: Wcoef
        rides in EVERY block's entry list and `D.instNe` supplies one.
hypothesis_fields: explicit `RegP S D` only.
-/
import Mathlib
import LeanUrat.MovesU.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesU

variable {n p : ℕ} {S : SolveData n} {D : RegData p}

/-- Q(p) contains p itself: `pool_eq` + `one_mem_depthSet` (p = p^1). Never-vacuous. -/
theorem RegData.pool_self_mem (D : RegData p) : p ∈ D.Pool := by
  rw [D.pool_eq]
  exact Finset.mem_image.mpr ⟨1, D.one_mem_depthSet, pow_one p⟩

/-- The generic (r2) accessor: every member of the DEFINED entry list E(e) is defined
    at every pool value and agrees with the ACT active value. -/
theorem RegP.entry_agree (h : RegP S D) {q₀ : ℕ} (hq : q₀ ∈ D.Pool) (e : D.Block)
    {g : RatFunc ℚ} (hg : g ∈ D.entryList e) :
    DefinedAt g (q₀ : ℚ) ∧ g.eval (RingHom.id ℚ) (q₀ : ℚ) = D.act g q₀ :=
  (h.1 q₀ hq e).2 g hg

/-- (r1): the full determinant (junk blocks included) is defined and ≠ 0 at every
    pool value. -/
theorem RegP.det_ne_zero (h : RegP S D) {q₀ : ℕ} (hq : q₀ ∈ D.Pool) (e : D.Block) :
    letI := D.instBi e; letI := D.instBd e
    DefinedAt (Matrix.det (1 - D.K e)) (q₀ : ℚ) ∧
      (Matrix.det (1 - D.K e)).eval (RingHom.id ℚ) (q₀ : ℚ) ≠ 0 :=
  (h.1 q₀ hq e).1

/-- Ruling (D)'s EVALUABILITY accessor: under (REG-p) the literal R_σ(p) is DEFINED. -/
theorem RegP.R_defined (h : RegP S D) (σ : SplittingType n) :
    DefinedAt (S.R σ) (p : ℚ) :=
  h.2.1 σ

/-- The RETYPE's SQ.4 ACTIVE-VALUE AGREEMENT accessor (ratification CRITICAL 5):
    under (REG-p) the literal evaluation of R_σ at p IS its ACT active value. -/
theorem RegP.R_agree (h : RegP S D) (σ : SplittingType n) :
    (S.R σ).eval (RingHom.id ℚ) (p : ℚ) = D.act (S.R σ) p :=
  h.2.2 σ

/-- (r2) at the K_e family: each matrix entry. -/
theorem RegP.K_agree (h : RegP S D) {q₀ : ℕ} (hq : q₀ ∈ D.Pool) (e : D.Block)
    (i j : D.bidx e) :
    DefinedAt (D.K e i j) (q₀ : ℚ) ∧
      (D.K e i j).eval (RingHom.id ℚ) (q₀ : ℚ) = D.act (D.K e i j) q₀ := by
  apply h.entry_agree hq e
  unfold RegData.entryList
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inl ⟨(i, j), rfl⟩)))))

/-- (r2) at the b_e^{term,fin} family. -/
theorem RegP.bterm_agree (h : RegP S D) {q₀ : ℕ} (hq : q₀ ∈ D.Pool) (e : D.Block)
    (i : D.bidx e) :
    DefinedAt (D.bterm e i) (q₀ : ℚ) ∧
      (D.bterm e i).eval (RingHom.id ℚ) (q₀ : ℚ) = D.act (D.bterm e i) q₀ := by
  apply h.entry_agree hq e
  unfold RegData.entryList
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩)))))

/-- (r2) at the b_e^split family. -/
theorem RegP.bsplit_agree (h : RegP S D) {q₀ : ℕ} (hq : q₀ ∈ D.Pool) (e : D.Block)
    (i : D.bidx e) :
    DefinedAt (D.bsplit e i) (q₀ : ℚ) ∧
      (D.bsplit e i).eval (RingHom.id ℚ) (q₀ : ℚ) = D.act (D.bsplit e i) q₀ := by
  apply h.entry_agree hq e
  unfold RegData.entryList
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))))

/-- (r2) at the per-cell J family (CL-18), ∀ j : JIdx e. -/
theorem RegP.Jcell_agree (h : RegP S D) {q₀ : ℕ} (hq : q₀ ∈ D.Pool) (e : D.Block)
    (j : D.JIdx e) :
    DefinedAt (D.Jcell e j) (q₀ : ℚ) ∧
      (D.Jcell e j).eval (RingHom.id ℚ) (q₀ : ℚ) = D.act (D.Jcell e j) q₀ := by
  apply h.entry_agree hq e
  unfold RegData.entryList
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inl (Or.inr ⟨j, rfl⟩)))

/-- (r2) at the ι_e family. -/
theorem RegP.iota_agree (h : RegP S D) {q₀ : ℕ} (hq : q₀ ∈ D.Pool) (e : D.Block)
    (i : D.bidx e) :
    DefinedAt (D.iota e i) (q₀ : ℚ) ∧
      (D.iota e i).eval (RingHom.id ℚ) (q₀ : ℚ) = D.act (D.iota e i) q₀ := by
  apply h.entry_agree hq e
  unfold RegData.entryList
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inl (Or.inl (Or.inr ⟨i, rfl⟩))

/-- (r2) at the W_Ŝ family (CL-17), ∀ w : WIdx (block-free: Wcoef rides in every
    block's entry list; `D.instNe` supplies one). -/
theorem RegP.Wcoef_agree (h : RegP S D) {q₀ : ℕ} (hq : q₀ ∈ D.Pool) (w : D.WIdx) :
    DefinedAt (D.Wcoef w) (q₀ : ℚ) ∧
      (D.Wcoef w).eval (RingHom.id ℚ) (q₀ : ℚ) = D.act (D.Wcoef w) q₀ := by
  apply h.entry_agree hq D.instNe.some
  unfold RegData.entryList
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inl (Or.inr ⟨w, rfl⟩)

/-- (r2) at the β legs, ∀ leg, ∀ δ ∈ depthSet — the per-pool coverage (ruling (C)). -/
theorem RegP.betaLeg_agree (h : RegP S D) {q₀ : ℕ} (hq : q₀ ∈ D.Pool) (e : D.Block)
    (l : D.legIdx e) {δ : ℕ} (hδ : δ ∈ D.depthSet) :
    DefinedAt (D.betaLeg e l δ) (q₀ : ℚ) ∧
      (D.betaLeg e l δ).eval (RingHom.id ℚ) (q₀ : ℚ) = D.act (D.betaLeg e l δ) q₀ := by
  apply h.entry_agree hq e
  unfold RegData.entryList
  simp only [Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and]
  exact Or.inr ⟨δ, hδ, l, rfl⟩

end LeanUrat.MovesU
