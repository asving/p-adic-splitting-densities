/-
Unit `n2_det` (easy; the NOTE-W6 geometric-series check — retagged, Fable#8-O-4:
the note's W6 display, unrelated to the pin W-6 = AVAgree) —
`(1 - Kmat).det = (q³−1)/q³ ≠ 0`.  Also carries `n2hdet`, the DetHyp term the
downstream checks consume (block 1: Kmat = 0, det = 1).
-/
import LeanUrat.MovesS.N2PolyGeom
import LeanUrat.MovesS.N2ScsData

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

/-- At the block-2 layer the state space is a singleton and the only kcol column
is the o_K outcome, so the kernel matrix's single entry is the o_K burden. -/
private lemma n2_Kmat2_entry (hK : KmatHyp n2T 2) :
    Kmat n2T n2RB 2 hK n2τ n2τ = (n2RB.tgP 2 n2τ n2oK).val := by
  haveI : Subsingleton (n2T.State 2) := inferInstanceAs (Subsingleton Unit)
  obtain ⟨hrK, hrSpl, hrIn, _, _, _, _, hexh, _, _, _, _⟩ := n2_shape
  unfold Kmat
  rw [Finset.sum_eq_single n2oK]
  · simp only [dif_pos hrK]
    split_ifs with hc
    · rfl
    · exact absurd (Subsingleton.elim _ _) hc
  · intro o _ hne
    apply dif_neg
    rcases hexh o with h | h | h
    · exact absurd h hne
    · rw [h, hrSpl]; decide
    · rw [h, hrIn]; decide
  · intro h; exact absurd (Finset.mem_univ n2oK) h

/-- At the block-1 layer every outcome is terminal (route `termFin`), so the
kernel matrix vanishes identically. -/
private lemma n2_Kmat1_zero (hK : KmatHyp n2T 1) (a b : n2T.State 1) :
    Kmat n2T n2RB 1 hK a b = 0 := by
  obtain ⟨_, _, _, _, _, _, _, _, _, _, _, hlayer1⟩ := n2_shape
  unfold Kmat
  apply Finset.sum_eq_zero
  intro o _
  apply dif_neg
  rw [(hlayer1 a o).1]
  decide

theorem n2_det (he : 2 ∈ Finset.Icc 1 2) :
    (1 - Kmat n2T n2RB 2 (n2hK 2 he)).det
      = algebraMap (Polynomial ℚ) Qq (X ^ 3 - 1) / algebraMap (Polynomial ℚ) Qq (X ^ 3) ∧
    (1 - Kmat n2T n2RB 2 (n2hK 2 he)).det ≠ 0 := by
  haveI : Subsingleton (n2T.State 2) := inferInstanceAs (Subsingleton Unit)
  have hX : (algebraMap (Polynomial ℚ) Qq X) ≠ 0 :=
    RatFunc.algebraMap_ne_zero Polynomial.X_ne_zero
  have ht : (algebraMap (Polynomial ℚ) Qq X) ^ 3 ≠ 0 := pow_ne_zero 3 hX
  have hden : algebraMap (Polynomial ℚ) Qq (X ^ 3) ≠ 0 :=
    RatFunc.algebraMap_ne_zero (pow_ne_zero 3 Polynomial.X_ne_zero)
  have hpoly : (X ^ 3 - 1 : Polynomial ℚ) ≠ 0 := by
    intro hz
    have h3 : (X ^ 3 - 1 : Polynomial ℚ).coeff 3 = 1 := by
      simp [Polynomial.coeff_X_pow, Polynomial.coeff_sub, Polynomial.coeff_one]
    rw [hz] at h3
    simp at h3
  have hnum : algebraMap (Polynomial ℚ) Qq (X ^ 3 - 1) ≠ 0 :=
    RatFunc.algebraMap_ne_zero hpoly
  have heq : (1 - Kmat n2T n2RB 2 (n2hK 2 he)).det
      = algebraMap (Polynomial ℚ) Qq (X ^ 3 - 1) / algebraMap (Polynomial ℚ) Qq (X ^ 3) := by
    rw [Matrix.det_eq_elem_of_subsingleton _ n2τ, Matrix.sub_apply, Matrix.one_apply_eq,
        n2_Kmat2_entry, n2_polygeom_data.1]
    unfold qX
    simp only [map_sub, map_one, map_pow, inv_pow]
    field_simp
  exact ⟨heq, by rw [heq]; exact div_ne_zero hnum hden⟩

theorem n2hdet : DetHyp n2T n2RB n2hK := by
  intro e he
  obtain ⟨h1, h2⟩ := Finset.mem_Icc.mp he
  have hcase : e = 1 ∨ e = 2 := by omega
  rcases hcase with rfl | rfl
  · have hK0 : Kmat n2T n2RB 1 (n2hK 1 he) = 0 := by
      funext a b
      simpa using n2_Kmat1_zero (n2hK 1 he) a b
    rw [hK0, sub_zero, Matrix.det_one]
    exact one_ne_zero
  · exact (n2_det he).2

end LeanUrat.MovesS
