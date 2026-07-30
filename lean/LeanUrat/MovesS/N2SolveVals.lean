/-
Unit `n2_solve_vals` (easy; NOTE-W6 check) — the reduced solve entries
β_{(1,2)} = (q+1)/(q²+q+1), β_{(1,1)²} = q²/(q²+q+1) — the note-displayed
denominator EXACTLY (`field_simp` over `RatFunc ℚ`).
-/
import LeanUrat.MovesS.N2Det
import LeanUrat.MovesS.BlockSolve

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial Matrix

/-- `q = X` is nonzero in `ℚ(q)`. -/
private theorem qX_ne : algebraMap (Polynomial ℚ) Qq X ≠ 0 :=
  RatFunc.algebraMap_ne_zero X_ne_zero

/-- `q⁻¹ − q⁻³` as a reduced fraction over `q³`. -/
private theorem qinv12 : qX⁻¹ - qX⁻¹ ^ 3
    = algebraMap (Polynomial ℚ) Qq (X ^ 2 - 1) / algebraMap (Polynomial ℚ) Qq (X ^ 3) := by
  rw [qX]
  simp only [map_sub, map_pow, map_one]
  field_simp [qX_ne]

/-- `1 − q⁻¹` as a reduced fraction over `q`. -/
private theorem qinv11 : (1 : Qq) - qX⁻¹
    = algebraMap (Polynomial ℚ) Qq (X - 1) / algebraMap (Polynomial ℚ) Qq X := by
  rw [qX, eq_div_iff qX_ne]
  simp only [map_sub, map_one]
  rw [sub_mul, one_mul, inv_mul_cancel₀ qX_ne]

/-- The solve denominator `q² + q + 1` is nonzero in `ℚ(q)`. -/
private theorem qden_ne :
    (algebraMap (Polynomial ℚ) Qq X) ^ 2 + algebraMap (Polynomial ℚ) Qq X + 1 ≠ 0 := by
  have hne : (X ^ 2 + X + 1 : Polynomial ℚ) ≠ 0 := by
    intro h
    simpa using congrArg (Polynomial.eval (0 : ℚ)) h
  have h := RatFunc.algebraMap_ne_zero (K := ℚ) (x := X ^ 2 + X + 1) hne
  simpa [map_add, map_pow, map_one] using h

/-- The block-2 state layer is a singleton: every state equals `n2τ`. -/
private theorem n2state_eq (τ : n2T.State 2) : τ = n2τ := by
  obtain ⟨_, _, _, _, _, _, _, _, _, hstate, _, _⟩ := n2_shape
  exact hstate τ

/-- No block-2 outcome is a split outcome. -/
private theorem n2_splitOuts_empty : splitOuts n2T 2 n2τ = ∅ := by
  apply Finset.eq_empty_of_forall_notMem
  intro o
  simp only [splitOuts, Set.mem_toFinset, Set.mem_setOf_eq]
  fin_cases o <;> decide

/-- The generic 1×1 triangular solve: if `A *ᵥ w = b` and `A` is invertible then
`A⁻¹ *ᵥ b = w`. -/
private theorem inv_mulVec_of_mulVec_eq {ι R : Type*} [Fintype ι] [DecidableEq ι]
    [CommRing R] {A : Matrix ι ι R} (hA : IsUnit A.det) {b w : ι → R}
    (h : A *ᵥ w = b) : A⁻¹ *ᵥ b = w := by
  rw [← h, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul A hA, Matrix.one_mulVec]

/-- `(1 - K)` diagonal entry at the singleton state, read off `n2_det` via the 1×1
determinant. -/
private theorem n2_diag (he : 2 ∈ Finset.Icc 1 2) :
    (1 - Kmat n2T n2RB 2 (n2hK 2 he)) n2τ n2τ
      = algebraMap (Polynomial ℚ) Qq (X ^ 3 - 1) / algebraMap (Polynomial ℚ) Qq (X ^ 3) := by
  haveI : Unique (n2T.State 2) := ⟨⟨n2τ⟩, n2state_eq⟩
  have h := (n2_det he).1
  rw [Matrix.det_unique] at h
  exact h

/-- b_2^{term,fin}({(1,2)}) = q⁻¹ − q⁻³. -/
private theorem n2_bTerm12 :
    bTerm n2T n2RB 2 {n2v12} n2τ = qX⁻¹ - qX⁻¹ ^ 3 := by
  obtain ⟨hrK, hrSpl, hrIn, hvSpl, hvIn, _, _, _, _, _, _, _⟩ := n2_shape
  have hpg := n2_polygeom_data
  have h0 : routeOf (n2T.odata 2 n2τ (0 : Fin 3)) = .kcol := hrK
  have v1 : (n2T.odata 2 n2τ (1 : Fin 3)).verdicts = {n2v11, n2v11} := hvSpl
  have h2 : routeOf (n2T.odata 2 n2τ (2 : Fin 3)) = .termFin := hrIn
  have v2 : (n2T.odata 2 n2τ (2 : Fin 3)).verdicts = {n2v12} := hvIn
  have t2 : n2RB.TG 2 n2τ (2 : Fin 3) = qX⁻¹ - qX⁻¹ ^ 3 := hpg.2.2.1
  simp only [bTerm]
  show (∑ o : Fin 3, if routeOf (n2T.odata 2 n2τ o) = Route.termFin ∧
      (n2T.odata 2 n2τ o).verdicts = {n2v12} then n2RB.TG 2 n2τ o else 0)
      = qX⁻¹ - qX⁻¹ ^ 3
  rw [Fin.sum_univ_three]
  have c0 : ¬ (routeOf (n2T.odata 2 n2τ (0 : Fin 3)) = .termFin ∧
      (n2T.odata 2 n2τ (0 : Fin 3)).verdicts = {n2v12}) := by
    rw [h0]; rintro ⟨hc, _⟩; exact absurd hc (by decide)
  have c1 : ¬ (routeOf (n2T.odata 2 n2τ (1 : Fin 3)) = .termFin ∧
      (n2T.odata 2 n2τ (1 : Fin 3)).verdicts = {n2v12}) := by
    rw [v1]; rintro ⟨_, hv⟩
    exact absurd hv (by intro h; simpa using congrArg Multiset.card h)
  have c2 : routeOf (n2T.odata 2 n2τ (2 : Fin 3)) = .termFin ∧
      (n2T.odata 2 n2τ (2 : Fin 3)).verdicts = {n2v12} := ⟨h2, v2⟩
  rw [if_neg c0, if_neg c1, if_pos c2, t2, zero_add, zero_add]

/-- b_2^{term,fin}({(1,1),(1,1)}) = 1 − q⁻¹. -/
private theorem n2_bTerm11 :
    bTerm n2T n2RB 2 {n2v11, n2v11} n2τ = 1 - qX⁻¹ := by
  obtain ⟨hrK, hrSpl, hrIn, hvSpl, hvIn, _, _, _, _, _, _, _⟩ := n2_shape
  have hpg := n2_polygeom_data
  have h0 : routeOf (n2T.odata 2 n2τ (0 : Fin 3)) = .kcol := hrK
  have h1 : routeOf (n2T.odata 2 n2τ (1 : Fin 3)) = .termFin := hrSpl
  have v1 : (n2T.odata 2 n2τ (1 : Fin 3)).verdicts = {n2v11, n2v11} := hvSpl
  have v2 : (n2T.odata 2 n2τ (2 : Fin 3)).verdicts = {n2v12} := hvIn
  have t1 : n2RB.TG 2 n2τ (1 : Fin 3) = 1 - qX⁻¹ := hpg.2.1
  simp only [bTerm]
  show (∑ o : Fin 3, if routeOf (n2T.odata 2 n2τ o) = Route.termFin ∧
      (n2T.odata 2 n2τ o).verdicts = {n2v11, n2v11} then n2RB.TG 2 n2τ o else 0)
      = 1 - qX⁻¹
  rw [Fin.sum_univ_three]
  have c0 : ¬ (routeOf (n2T.odata 2 n2τ (0 : Fin 3)) = .termFin ∧
      (n2T.odata 2 n2τ (0 : Fin 3)).verdicts = {n2v11, n2v11}) := by
    rw [h0]; rintro ⟨hc, _⟩; exact absurd hc (by decide)
  have c1 : routeOf (n2T.odata 2 n2τ (1 : Fin 3)) = .termFin ∧
      (n2T.odata 2 n2τ (1 : Fin 3)).verdicts = {n2v11, n2v11} := ⟨h1, v1⟩
  have c2 : ¬ (routeOf (n2T.odata 2 n2τ (2 : Fin 3)) = .termFin ∧
      (n2T.odata 2 n2τ (2 : Fin 3)).verdicts = {n2v11, n2v11}) := by
    rw [v2]; rintro ⟨_, hv⟩
    exact absurd hv (by intro h; simpa using congrArg Multiset.card h)
  rw [if_neg c0, if_pos c1, if_neg c2, t1, zero_add, add_zero]

/-- The split exit vector vanishes at block 2 (no split outcomes). -/
private theorem n2_bSplit_zero (he : 2 ∈ Finset.Icc 1 2)
    (βlt : ∀ e', e' < 2 → n2T.State e' → Multiset n2T.VType → Qq)
    (σ' : Multiset n2T.VType) :
    bSplit n2T n2RB n2hdc 2 he βlt σ' n2τ = 0 := by
  rw [bSplit_def, n2_splitOuts_empty, Finset.sum_empty]

theorem n2_solve_vals (he : 2 ∈ Finset.Icc 1 2) :
    blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he n2τ {n2v12}
      = algebraMap (Polynomial ℚ) Qq (X + 1)
        / algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1) ∧
    blockSolve n2T n2RB n2hdc n2hK n2hdet 2 he n2τ {n2v11, n2v11}
      = algebraMap (Polynomial ℚ) Qq (X ^ 2)
        / algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1) := by
  haveI : Unique (n2T.State 2) := ⟨⟨n2τ⟩, n2state_eq⟩
  have hunit : IsUnit ((1 - Kmat n2T n2RB 2 (n2hK 2 he)).det) :=
    isUnit_iff_ne_zero.mpr (n2hdet 2 he)
  constructor
  · rw [blockSolve_eq]
    refine congrFun (inv_mulVec_of_mulVec_eq hunit
      (w := fun _ => algebraMap (Polynomial ℚ) Qq (X + 1)
        / algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1)) ?_) n2τ
    funext τ
    rw [n2state_eq τ]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_unique, Pi.add_apply]
    rw [n2state_eq (default : n2T.State 2), n2_diag he, n2_bTerm12, n2_bSplit_zero he,
      add_zero, qinv12]
    simp only [map_add, map_sub, map_pow, map_one]
    rw [div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 3 qX_ne) qden_ne) (pow_ne_zero 3 qX_ne)]
    ring
  · rw [blockSolve_eq]
    refine congrFun (inv_mulVec_of_mulVec_eq hunit
      (w := fun _ => algebraMap (Polynomial ℚ) Qq (X ^ 2)
        / algebraMap (Polynomial ℚ) Qq (X ^ 2 + X + 1)) ?_) n2τ
    funext τ
    rw [n2state_eq τ]
    simp only [Matrix.mulVec, dotProduct, Fintype.sum_unique, Pi.add_apply]
    rw [n2state_eq (default : n2T.State 2), n2_diag he, n2_bTerm11, n2_bSplit_zero he,
      add_zero, qinv11]
    simp only [map_add, map_sub, map_pow, map_one]
    rw [div_mul_div_comm,
      div_eq_div_iff (mul_ne_zero (pow_ne_zero 3 qX_ne) qden_ne) qX_ne]
    ring

end LeanUrat.MovesS
