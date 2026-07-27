/-
Unit U-12 `powSubst` (medium) — the base-change substitution q ↦ q^δ on ℚ(q).
moves_ref: "composed with q ↦ q^{δ_j} … ([2r] (e2), δ absolute)".
sketch: `IsFractionRing.lift` over `aeval (X^(δ:ℕ))`; δ ≥ 1 ⟹ nonzero ↦ nonzero.
δ : ℕ+ (δ = 0 unrepresentable — D6).
-/
import LeanUrat.MovesS.Defs

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS
open Polynomial

noncomputable def powSubst (δ : ℕ+) : Qq →+* Qq :=
  sorry

theorem powSubst_X (δ : ℕ+) :
    powSubst δ (algebraMap (Polynomial ℚ) Qq X) =
      algebraMap (Polynomial ℚ) Qq (X ^ (δ : ℕ)) :=
  sorry

theorem powSubst_C (δ : ℕ+) (c : ℚ) :
    powSubst δ (RatFunc.C c) = RatFunc.C c :=
  sorry

end LeanUrat.MovesS
