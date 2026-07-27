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

/-- The polynomial substitution `X ↦ X^δ` as a ring hom into `Qq`, i.e.
`Polynomial.expand ℚ δ` followed by the inclusion into the fraction field. It is injective
(δ ≥ 1), so it lifts to the fraction field below. -/
noncomputable def powSubstAux (δ : ℕ+) : Polynomial ℚ →+* Qq :=
  (algebraMap (Polynomial ℚ) Qq).comp (Polynomial.expand ℚ (δ : ℕ)).toRingHom

theorem powSubstAux_injective (δ : ℕ+) : Function.Injective (powSubstAux δ) := by
  refine (IsFractionRing.injective (Polynomial ℚ) Qq).comp ?_
  exact Polynomial.expand_injective δ.pos

noncomputable def powSubst (δ : ℕ+) : Qq →+* Qq :=
  IsFractionRing.lift (powSubstAux_injective δ)

theorem powSubst_X (δ : ℕ+) :
    powSubst δ (algebraMap (Polynomial ℚ) Qq X) =
      algebraMap (Polynomial ℚ) Qq (X ^ (δ : ℕ)) := by
  rw [powSubst, IsFractionRing.lift_algebraMap, powSubstAux, RingHom.comp_apply]
  change algebraMap (Polynomial ℚ) Qq (Polynomial.expand ℚ (δ : ℕ) X) = _
  rw [Polynomial.expand_X]

theorem powSubst_C (δ : ℕ+) (c : ℚ) :
    powSubst δ (RatFunc.C c) = RatFunc.C c := by
  rw [← RatFunc.algebraMap_C, powSubst, IsFractionRing.lift_algebraMap, powSubstAux,
    RingHom.comp_apply]
  change algebraMap (Polynomial ℚ) Qq (Polynomial.expand ℚ (δ : ℕ) (Polynomial.C c)) = _
  rw [Polynomial.expand_C]

end LeanUrat.MovesS
