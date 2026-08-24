/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C52
import Uniformity.ChapC.C131k
import Uniformity.ChapC.C131p

/-!
# Uniformity.ChapC.C131u — the `DvAbove` bridge and shadow-discrepancy interface

**Chapter C, NODES C.131u′–v′**
(`docs/in-progress/DV_GRADED_ENGINE_V2_2026-08-24.md` §3.7–§3.8 and §5).

C.131u′ lands the direction of the all-coefficient bridge actually used by C.52: a floor
for every scalar coefficient of every canonical `F.key`-digit implies `DvAbove`.  The rejected
converse from §3.7 is not asserted.

C.131v′ does not land in this unit.  The requested semantic target is the reduced normal form
produced by the tagged structural census, but no such census object or erasure theorem is among
the stated dependencies C.71 and C.131k′–l′.  Those dependencies provide `shadowDev`, `xNF`,
and `outerNF`, but no declaration relating the shadow division tower to the honest division
tower.  This is exactly the missing identification recorded as OPEN in §3.8 (`Cnv13`), and a
definition obtained by applying `xNF` directly to the desired discrepancy would be circular
rather than the census identification.

## Status

* C.131u′: LANDED, Lean core only.
* C.131v′: BLOCKED on the tagged-census normal-form object and its erasure semantics
  (C.131m′'s advertised `tagged paid-branch recursion and erasure theorem`).
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C131u

open Polynomial IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C131p

variable {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] {π : O}

/-! ## C.131u′ — all scalar coefficient floors imply `DvAbove` -/

/-- **Cnv12′.** If every scalar coefficient in every canonical `F.key`-digit of `A` has
the cleared two-index weight at least `w`, then all level-one slots of `A` lie above `w`.

The positivity hypothesis is necessary for commuting the scalar `e₂` with the empty
`Finset.inf`: at scalar zero, `0 • ⊤ = 0`. -/
theorem dvAbove_of_forall_coeff_floor (F : KeyFrame O π) (A : Polynomial O)
    (u₂ e₂ : ℕ) (w : ℕ∞) (he₂ : 0 < e₂)
    (hfloor : ∀ b a : ℕ,
      w ≤ (F.e₁ * e₂) • addVal O ((dev F.key A b).coeff a) +
        (a * (e₂ * F.h) + b * u₂ : ℕ∞)) :
    DvAbove F A u₂ e₂ w := by
  intro b
  rw [dvHgt_eq_coeff_inf, enat_nsmul_finset_inf _ _ he₂,
    enat_finset_inf_add]
  refine Finset.le_inf fun a _ ↦ ?_
  have hnorm :
      e₂ • (F.e₁ • addVal O ((dev F.key A b).coeff a) + (F.h * a : ℕ∞)) +
          (u₂ * b : ℕ∞) =
        (F.e₁ * e₂) • addVal O ((dev F.key A b).coeff a) +
          (a * (e₂ * F.h) + b * u₂ : ℕ∞) := by
    simp only [nsmul_eq_mul, Nat.cast_mul]
    ring
  rw [hnorm]
  exact hfloor b a

end Uniformity.Density.Tower.C131u

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C131u.dvAbove_of_forall_coeff_floor

end AxCheck
