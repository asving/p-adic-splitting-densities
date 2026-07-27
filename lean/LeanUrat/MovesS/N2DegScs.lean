/-
Unit U-29b3 `n2_degcons_scs` (easy) — DegCons + SCSData LAWS on the three-outcome
roster, window data CORRECTED (R35, Fable#5-F1): sizes (2), (1,1), (2) with sums
≤ 2; (m,c) routing (1,1)/(2,0)/(1,0); SCS at o_K with W = 2, D = 1, ℓ = 1, g = 1,
μ = 1 (window_comp: 2 = 2·1 + 0 ✓; res_sum: g·μ = 1 = ℓ ✓; W′ = μ = 1,
D′ = e·g·D = 2, W′D′ = 2 = WD = the member's size ✓ — U-5's law exact).  The
REV-7 μ = 2 conflated the ROOT-ENTRANCE typing with the kcol in-block window.
-/
import LeanUrat.MovesS.N2ScsData

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem n2_degcons_scs :
    (((n2T.odata 2 n2τ n2oK).mem.map Member.size).sum ≤ 2 ∧
     ((n2T.odata 2 n2τ n2oSpl).mem.map Member.size).sum ≤ 2 ∧
     ((n2T.odata 2 n2τ n2oIn).mem.map Member.size).sum ≤ 2) ∧
    ((n2T.odata 2 n2τ n2oK).m = 1 ∧ (n2T.odata 2 n2τ n2oK).c = 1) ∧
    ((n2T.odata 2 n2τ n2oSpl).m = 2 ∧ (n2T.odata 2 n2τ n2oSpl).c = 0) ∧
    ((n2T.odata 2 n2τ n2oIn).m = 1 ∧ (n2T.odata 2 n2τ n2oIn).c = 0) ∧
    (n2SCS.W 2 n2τ n2oK = 2 ∧ n2SCS.D 2 n2τ n2oK = 1 ∧
     n2SCS.ℓ 2 n2τ n2oK = 1 ∧ n2SCS.g 2 n2τ n2oK = 1 ∧
     n2SCS.μsel 2 n2τ n2oK = 1 ∧ n2SCS.flankWidth 2 n2τ n2oK = 0 ∧
     n2SCS.W' 2 n2τ n2oK = 1 ∧ n2SCS.D' 2 n2τ n2oK = 2) :=
  sorry

end LeanUrat.MovesS
