/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import UniformityCheck.N3Struct
import Uniformity.StrongHensel
import Uniformity.Density.TypeOfInvariance

/-!
# UniformityCheck.P5Consume — the `n = 3` consumers of the `UNIFORMITY-P5` infrastructure

`leanfinal` gained three general theorems in unit `UNIFORMITY-P5`
(`leanfinal/notes/P5_INFRA_2026-08-14.md`):

* `Uniformity.Hensel.strongHensel` (HYP.04) — Hensel with a non-unit derivative;
* `Uniformity.Density.typeOf_shift` (HYP.05) — `typeOf (F(X + c)) = typeOf F`;
* `Uniformity.Density.typeOf_scale` (HYP.06) — the `π`-power extraction relation.

This file wires each one into the shape the `n = 3` triple-root recursion of
`notes/N3_CHECK_2026-08-13.md` §9.4 asks for, and nothing else. Each is one line on top of the
general theorem; all the mathematics is in `leanfinal`.

The §9.4 table row by row:

| polygon | verdict | tool |
|---|---|---|
| `v(B₀) = 1` after recentring at `c` | `{(3,1)}` | **`typeOf_ram3_of_eisenstein_shift`** (was blocked on shift invariance) |
| single side of integral slope `m` | recurse on the rescaled cubic | **`typeOf_cubic_scale`** (was blocked on scale invariance) |
| two or three sides | a root with non-unit derivative | **`exists_cubic_root_strong`** (was blocked on strong Hensel) |

## Status

Sorry-free; footprints Lean core only (`AxCheck` block at the foot).
-/

set_option linter.style.longLine false

namespace UniformityCheck

open Uniformity Uniformity.Density IsLocalRing Polynomial

section Consume

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/-- **The recentred Eisenstein certificate.** `typeOf_ram3_of_eisenstein` only fires on a cubic
whose *own* coefficients are Eisenstein; the triple-root recursion produces an Eisenstein cubic
only after recentring at a lift `c` of the residual triple root. Shift invariance closes the gap:
if the recentred coefficient vector `b` is Eisenstein, the original cubic is totally ramified. -/
theorem typeOf_ram3_of_eisenstein_shift {a b : Fin 3 → O} (c : O)
    (hshift : monicPoly b = (monicPoly a).comp (X + C c))
    (h0 : b 0 ∈ maximalIdeal O) (h0' : b 0 ∉ (maximalIdeal O) ^ 2)
    (h1 : b 1 ∈ maximalIdeal O) (h2 : b 2 ∈ maximalIdeal O) :
    typeOf (monicPoly a) = c3ram := by
  rw [← typeOf_shift (monicPoly_monic a) c, ← hshift]
  exact typeOf_ram3_of_eisenstein h0 h0' h1 h2

/-- **The depth-reduction step.** If the cubic `monicPoly a` becomes `monicPoly b` after the
integral-slope extraction `X = π^m Y` — i.e. `(monicPoly a)(π^m Y) = π^(3m)·(monicPoly b)(Y)` —
then the two have the same splitting type, so the recursion may descend to `b`. -/
theorem typeOf_cubic_scale {π : O} (hπ : Irreducible π) {a b : Fin 3 → O} (m : ℕ)
    (hcomp : (monicPoly a).comp (C (π ^ m) * X) = C (π ^ (m * 3)) * monicPoly b) :
    typeOf (monicPoly a) = typeOf (monicPoly b) := by
  refine typeOf_scale hπ (monicPoly_monic b) ?_ m ?_
  · rw [monicPoly_natDegree, monicPoly_natDegree]
  · rw [monicPoly_natDegree]; exact hcomp

variable [IsAdicComplete (maximalIdeal O) O]

/-- **The two-or-three-sides branch.** A cubic with `v(F(x₀)) ≥ k > 2w = 2·v(F′(x₀))` has a root
at distance `≥ k - w` from `x₀`, unique in the disc of radius `> w`. This is the case the
coprime-factorization Hensel of `Uniformity.HenselFactorization` cannot reach (the residual
factorization is `X · X²`). -/
theorem exists_cubic_root_strong {π : O} (hπ : Irreducible π) {a : Fin 3 → O} {x₀ : O} {w k : ℕ}
    (hd : ∃ u : Oˣ, (monicPoly a).derivative.eval x₀ = π ^ w * u)
    (hv : π ^ k ∣ (monicPoly a).eval x₀) (hk : 2 * w < k) :
    ∃ r : O, (monicPoly a).eval r = 0 ∧ π ^ (k - w) ∣ r - x₀ ∧
      ∀ s : O, (monicPoly a).eval s = 0 → π ^ (w + 1) ∣ s - x₀ → s = r :=
  Hensel.strongHensel hπ hd hv hk

/-- The `addVal` phrasing of the same, matching `N3_CHECK` §9.4's own wording
`v(F(x₀)) > 2·v(F′(x₀)) = 2w ⟹ ∃ r, F(r) = 0 ∧ v(r − x₀) > w`. -/
theorem exists_cubic_root_strong_addVal {π : O} (hπ : Irreducible π) {a : Fin 3 → O} {x₀ : O}
    {w : ℕ}
    (hw : IsDiscreteValuationRing.addVal O ((monicPoly a).derivative.eval x₀) = (w : ℕ∞))
    (hgt : ((2 * w : ℕ) : ℕ∞) < IsDiscreteValuationRing.addVal O ((monicPoly a).eval x₀)) :
    ∃ r : O, (monicPoly a).eval r = 0 ∧
      (w : ℕ∞) < IsDiscreteValuationRing.addVal O (r - x₀) ∧
      ∀ s : O, (monicPoly a).eval s = 0 →
        (w : ℕ∞) < IsDiscreteValuationRing.addVal O (s - x₀) → s = r :=
  Hensel.strongHensel_addVal hπ hw hgt

end Consume

/-! ## Axiom census -/

section AxCheck

#print axioms UniformityCheck.typeOf_ram3_of_eisenstein_shift
#print axioms UniformityCheck.typeOf_cubic_scale
#print axioms UniformityCheck.exists_cubic_root_strong
#print axioms UniformityCheck.exists_cubic_root_strong_addVal

end AxCheck

end UniformityCheck
