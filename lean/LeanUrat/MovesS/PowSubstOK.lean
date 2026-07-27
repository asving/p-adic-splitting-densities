/-
Unit U-12b `powSubst_OKat_evalAt` (easy) — OK-membership and evaluation transport
along a base-change leg q₀ ↦ q₀^δ (serves R14).  sketch: the denominator of
`powSubst δ f` divides `f.denom.comp (X^δ)`, and `(f.denom.comp (X^δ)).eval q₀ =
f.denom.eval (q₀^δ) ≠ 0`; `Polynomial.eval_comp` + denominator divisibility under
ring homs.
-/
import LeanUrat.MovesS.Defs
import LeanUrat.MovesS.PowSubst

set_option linter.style.longLine false
set_option linter.style.header false
set_option linter.unusedVariables false
set_option maxHeartbeats 1000000

namespace LeanUrat.MovesS

theorem powSubst_OKat (δ : ℕ+) (q₀ : ℚ) (f : Qq) (h : f ∈ OKat (q₀ ^ (δ : ℕ))) :
    powSubst δ f ∈ OKat q₀ :=
  sorry

theorem powSubst_evalAt (δ : ℕ+) (q₀ : ℚ) (f : Qq) (h : f ∈ OKat (q₀ ^ (δ : ℕ))) :
    evalAt q₀ ⟨powSubst δ f, powSubst_OKat δ q₀ f h⟩ = evalAt (q₀ ^ (δ : ℕ)) ⟨f, h⟩ :=
  sorry

end LeanUrat.MovesS
