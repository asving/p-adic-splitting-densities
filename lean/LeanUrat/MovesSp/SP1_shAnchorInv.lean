/-
Unit Sp.shAnchorInv — moves_ref: "the anchored residual is SHIFT-INVARIANT:
R_anch := z^{−ord_z R}·R = Σ_k c_{j_k}·z^k in BOTH displays (relabeling p ↦ p + σ
multiplies R by z^σ, which the anchoring cancels), so λ, the selection, and
ℓ = deg R_anch never see σ."
deps: — (REUSES `Moves.HasAnchorK` — the corpus-link unit). sketch: unfold
HasAnchorK; `LaurentPolynomial.T_add`, `mul_assoc`. difficulty: medium.
-/
import LeanUrat.MovesSp.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesSp

theorem hasAnchorK_T_mul {K : Type*} [Field K] (x : LaurentPolynomial K)
    (a σ : ℤ) (R : Polynomial K) (h : Moves.HasAnchorK x a R) :
    Moves.HasAnchorK (LaurentPolynomial.T σ * x) (a + σ) R := by
  obtain ⟨h0, hx⟩ := h
  refine ⟨h0, ?_⟩
  rw [hx, ← mul_assoc, ← LaurentPolynomial.T_add, add_comm σ a]

end LeanUrat.MovesSp
