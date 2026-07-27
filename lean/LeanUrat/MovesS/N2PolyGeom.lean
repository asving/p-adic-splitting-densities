/-
Unit `n2_polygeom_data` (medium; S5 construction batch) — the RatBurdens instance
with the three PolyGeom presentations in the CORRECTED form (R30):
q⁻³ (qpow 3, geomDenoms ∅) · 1 − q⁻¹ = (X−1)/X (qpow 1) · q⁻¹ − q⁻³ = (X²−1)/X³
(qpow 3) — all inhabit PolyGeom under the restored X^b · ∏(1 − X^a) law.
-/
import LeanUrat.MovesS.N2Carriers

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

noncomputable def n2RB : RatBurdens n2T n2M := sorry

/-- The symbolic variable q (the RatFunc X). -/
noncomputable def qX : Qq := algebraMap (Polynomial ℚ) Qq Polynomial.X

theorem n2_polygeom_data :
    (n2RB.tgP 2 n2τ n2oK).val = qX⁻¹ ^ 3 ∧
    (n2RB.tgP 2 n2τ n2oSpl).val = 1 - qX⁻¹ ∧
    (n2RB.tgP 2 n2τ n2oIn).val = qX⁻¹ - qX⁻¹ ^ 3 ∧
    (n2RB.tgP 2 n2τ n2oK).qpow = 3 ∧
    (n2RB.tgP 2 n2τ n2oSpl).qpow = 1 ∧
    (n2RB.tgP 2 n2τ n2oIn).qpow = 3 ∧
    (n2RB.tgP 2 n2τ n2oK).geomDenoms = ∅ :=
  sorry

end LeanUrat.MovesS
