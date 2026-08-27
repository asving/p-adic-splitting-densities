/-
Copyright (c) 2026 Asvin G. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Asvin G
-/
import Uniformity.ChapC.C132kp2
import Uniformity.ChapC.C132kp4
import Uniformity.ChapC.C130lb

/-!
# Uniformity.ChapC.C132kp5 — irreducibility of μ₃ key polynomials

**[M3-KP5, 2026-08-27]** (`docs/in-progress/MU3_CAMPAIGN_2026-08-26.md` §6): every
`S2Mu3KeyPoly` is irreducible in `Polynomial O`.  This is the μ₃ instance of the landed
μ₂ factorization transport in `C130fd0`: μ₃-primality splits a factorization and
μ₃-minimality excludes either strictly smaller factor.  The monic Gauss bridge is reused
from `C130lb`, rather than introducing a further fraction-field citation.
-/

set_option linter.style.longLine false

namespace Uniformity.Density.Tower.C132kp5

open Polynomial IsLocalRing IsDiscreteValuationRing Uniformity.Density
open Uniformity.Density.Leaf Uniformity.Density.Tower
open Uniformity.Density.Tower.C130s2
open Uniformity.Density.Tower.C132kp0
open Uniformity.Density.Tower.C132kp2 Uniformity.Density.Tower.C132kp4

universe uKv

section S2

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Finite (ResidueField O)] (h2 : Irreducible (2 : O)) (hq : residueCard O = 2)

/-- Every μ₃ key polynomial is irreducible over `O`. -/
theorem s2Mu3_key_irreducible {g : Polynomial O} (hkey : S2Mu3KeyPoly h2 hq g) :
    Irreducible g := by
  obtain ⟨hmon, hmin, hirr⟩ := hkey
  refine ⟨fun hu => ?_, fun a b hab => ?_⟩
  · have hzero := Polynomial.natDegree_eq_zero_of_isUnit hu
    have hpos := hmin.1
    omega
  · by_contra hcon
    have hua : ¬ IsUnit a := fun ha => hcon (Or.inl ha)
    have hub : ¬ IsUnit b := fun hb => hcon (Or.inr hb)
    have hg0 : g ≠ 0 := hmon.ne_zero
    have ha0 : a ≠ 0 := by
      rintro rfl
      exact hg0 (by rw [hab, zero_mul])
    have hb0 : b ≠ 0 := by
      rintro rfl
      exact hg0 (by rw [hab, mul_zero])
    have hlc : a.leadingCoeff * b.leadingCoeff = 1 := by
      rw [← Polynomial.leadingCoeff_mul, ← hab]
      exact hmon.leadingCoeff
    have hdega : 0 < a.natDegree := by
      rcases Nat.eq_zero_or_pos a.natDegree with hzero | hpos
      · exfalso
        refine hua ?_
        have hCa : a = Polynomial.C (a.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hzero
        rw [hCa] at hlc
        rw [Polynomial.leadingCoeff_C] at hlc
        rw [hCa]
        exact Polynomial.isUnit_C.mpr (.of_mul_eq_one _ hlc)
      · exact hpos
    have hdegb : 0 < b.natDegree := by
      rcases Nat.eq_zero_or_pos b.natDegree with hzero | hpos
      · exfalso
        refine hub ?_
        have hCb : b = Polynomial.C (b.coeff 0) :=
          Polynomial.eq_C_of_natDegree_eq_zero hzero
        rw [hCb] at hlc
        rw [Polynomial.leadingCoeff_C] at hlc
        rw [hCb]
        exact Polynomial.isUnit_C.mpr (.of_mul_eq_one _ (by rw [mul_comm]; exact hlc))
      · exact hpos
    have hdeg : a.natDegree + b.natDegree = g.natDegree := by
      rw [hab, Polynomial.natDegree_mul ha0 hb0]
    have hself : S2Mu3Dvd h2 hq g (a * b) :=
      S2Mu3Dvd_of_dvd h2 hq (dvd_of_eq hab)
    rcases hirr.2.2 a b hself with hdvd | hdvd
    · exact hmin.2 a ha0 (by omega) hdvd
    · exact hmin.2 b hb0 (by omega) hdvd

/-- The landed monic Gauss transport specialized to a μ₃ key polynomial. -/
theorem s2Mu3_key_irreducible_of_fraction_map
    {Kv : Type uKv} [Field Kv] [Algebra O Kv] [IsFractionRing O Kv]
    {g : Polynomial O} (hkey : S2Mu3KeyPoly h2 hq g)
    (hfrac : Irreducible (g.map (algebraMap O Kv))) : Irreducible g :=
  irreducible_of_fraction_map_irreducible hkey.1 hfrac

/-- The carried key `Φ₂` is irreducible over `O`. -/
theorem s2Mu3_Φ₂_irreducible :
    Irreducible (s2DepthTwoKeyAt h2 hq 2 : Polynomial O) :=
  s2Mu3_key_irreducible h2 hq (s2Mu3KeyPoly_Φ₂ h2 hq)

end S2

end Uniformity.Density.Tower.C132kp5

/-! ## Axiom footprint -/

section AxCheck

#print axioms Uniformity.Density.Tower.C132kp5.s2Mu3_key_irreducible
#print axioms Uniformity.Density.Tower.C132kp5.s2Mu3_key_irreducible_of_fraction_map
#print axioms Uniformity.Density.Tower.C132kp5.s2Mu3_Φ₂_irreducible

end AxCheck
