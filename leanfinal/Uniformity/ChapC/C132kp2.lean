/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132kp1

/-!
# Uniformity.ChapC.C132kp2 — μ₃ residual primality and minimality

**[M3-KP2, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6):
an irreducible normalized μ₃ residual gives μ₃-irreducibility, while a nonunit normalized
residual gives μ₃-minimality in the degree-eight remainder scope.

Both transfers use M3-KP1's honest monic degree-`≤ 8` residual-divisibility equivalence.
The minimality argument only uses its forward direction: a nonzero polynomial of smaller
degree has unit normalized residual, so it cannot be μ₃-divisible by a nonunit residual.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132kp2

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2 Uniformity.Density.Tower.C130s6
open Uniformity.Density.Tower.C132nv0 Uniformity.Density.Tower.C132nv1
open Uniformity.Density.Tower.C132rp0 Uniformity.Density.Tower.C132rp1
open Uniformity.Density.Tower.C132rp2 Uniformity.Density.Tower.C132rp3
open Uniformity.Density.Tower.C132rp6 Uniformity.Density.Tower.C132rp7
open Uniformity.Density.Tower.C132rp8 Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C132kp1 Uniformity.Density.Tower.C80

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-! ## Irreducibility from an irreducible residual -/

/-- An irreducible normalized μ₃ residual makes the initial form μ₃-irreducible in the
monic degree-`≤ 8` scope. -/
theorem s2Mu3Irreducible_of_irreducible_normRes {g : Polynomial O} (hmon : g.Monic)
    (hdeg : g.natDegree ≤ 8) (hirr : Irreducible (s2Mu3NormRes h2 hq g)) :
    S2Mu3Irreducible h2 hq g := by
  refine ⟨hmon.ne_zero, ?_, ?_⟩
  · intro hone
    have hd := mu3NormRes_dvd_of_S2Mu3Dvd h2 hq hone
    rw [s2Mu3NormRes_one h2 hq] at hd
    exact hirr.not_isUnit (isUnit_of_dvd_one hd)
  · intro x y hxy
    have hd := mu3NormRes_dvd_of_S2Mu3Dvd h2 hq hxy
    rw [s2Mu3NormRes_mul h2 hq] at hd
    have hprime : Prime (s2Mu3NormRes h2 hq g) :=
      UniqueFactorizationMonoid.irreducible_iff_prime.mp hirr
    rcases hprime.2.2 _ _ hd with hdx | hdy
    · exact Or.inl (S2Mu3Dvd_of_mu3NormRes_dvd h2 hq hmon hdeg hirr.not_isUnit hdx)
    · exact Or.inr (S2Mu3Dvd_of_mu3NormRes_dvd h2 hq hmon hdeg hirr.not_isUnit hdy)

/-! ## Minimality from a nonunit residual -/

/-- A positive-degree polynomial of degree at most eight whose normalized μ₃ residual is not
a unit is μ₃-minimal. -/
theorem s2Mu3Minimal_of_not_isUnit_normRes {g : Polynomial O}
    (hpos : 0 < g.natDegree) (hdeg : g.natDegree ≤ 8)
    (hnu : ¬ IsUnit (s2Mu3NormRes h2 hq g)) :
    S2Mu3Minimal h2 hq g :=
  ⟨hpos, fun f hf0 hdegf hdvd =>
    hnu (isUnit_of_dvd_unit (mu3NormRes_dvd_of_S2Mu3Dvd h2 hq hdvd)
      (s2Mu3NormRes_isUnit_of_natDegree_lt_eight h2 hq hf0 (by omega)))⟩

/-- At the degree-eight μ₃ recipe size, irreducible normalized residual implies μ₃-minimality. -/
theorem s2Mu3Minimal_of_irreducible_normRes {g : Polynomial O}
    (hdeg : g.natDegree = 8) (hirr : Irreducible (s2Mu3NormRes h2 hq g)) :
    S2Mu3Minimal h2 hq g :=
  s2Mu3Minimal_of_not_isUnit_normRes h2 hq (by omega) (le_of_eq hdeg) hirr.not_isUnit

end S2

end Uniformity.Density.Tower.C132kp2

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132kp2.s2Mu3Irreducible_of_irreducible_normRes
#print axioms Uniformity.Density.Tower.C132kp2.s2Mu3Minimal_of_not_isUnit_normRes
#print axioms Uniformity.Density.Tower.C132kp2.s2Mu3Minimal_of_irreducible_normRes

end AxCheck
